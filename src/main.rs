// Rule 110 Cellular Automaton Visualizer
//
// Displays the evolution of a 1D Rule 110 cellular automaton as a 2D history.
// - System runs automatically and pauses while SPACE is held down
// - Release SPACE to resume computation and rendering (10 rows per frame)
// - Board starts with a single black cell and evolves infinitely
// - When the board fills up, it scrolls down (shifts up) and continues computing

use clap::Parser;
use gif::{Encoder as GifEncoder, Frame, Repeat};
use std::fs::File;
use std::io::BufWriter;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use vello::kurbo::RoundedRect;
use vello::peniko::Color;
use vello::{AaConfig, AaSupport, Renderer, RendererOptions, Scene};
use wgpu::util::TextureBlitter;
use winit::application::ApplicationHandler;
use winit::event::{ElementState, KeyEvent, WindowEvent};
use winit::event_loop::{ActiveEventLoop, ControlFlow, EventLoop, EventLoopProxy};
use winit::keyboard::{Key, NamedKey};
use winit::window::{Window, WindowId};

const CELL_SIZE: f64 = 4.0;
const WINDOW_WIDTH: u32 = 1600;
const WINDOW_HEIGHT: u32 = 1200;
const VISIBLE_BOARD_WIDTH: usize = (WINDOW_WIDTH as f64 / CELL_SIZE) as usize;
const VISIBLE_BOARD_HEIGHT: usize = (WINDOW_HEIGHT as f64 / CELL_SIZE) as usize;
// Compute board 10x wider than visible area (but same height)
const BOARD_WIDTH: usize = VISIBLE_BOARD_WIDTH * 10;
const BOARD_HEIGHT: usize = VISIBLE_BOARD_HEIGHT;
const STEPS_PER_FRAME: usize = 10; // Rows computed per frame

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Optional path to save the run as a GIF file
    #[arg(long, value_name = "FILE")]
    record_gif: Option<String>,

    /// Record every Nth frame to GIF (default: 10)
    #[arg(long, default_value = "10")]
    gif_frame_skip: usize,

    /// Number of pixels to scroll per arrow key press (default: 10)
    #[arg(long, default_value = "10")]
    scroll_step: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CellState {
    Zero,
    One,
    None,
}

impl CellState {
    fn color(self) -> Color {
        match self {
            CellState::Zero => Color::WHITE,
            CellState::One => Color::BLACK,
            CellState::None => Color::from_rgb8(220, 220, 220), // Light grey
        }
    }
}

#[derive(Clone)]
struct Board {
    cells: Vec<Vec<CellState>>,
    width: usize,
    height: usize,
    row_offset: usize, // Circular buffer offset: logical row 0 maps to cells[row_offset]
}

impl Board {
    fn new(width: usize, height: usize) -> Self {
        let mut cells = vec![vec![CellState::None; width]; height];

        // Init: first row is all zeros except rightmost position which is One
        for col in 0..width {
            if col == width - 1 {
                cells[0][col] = CellState::One;
            } else {
                cells[0][col] = CellState::Zero;
            }
        }

        Board {
            cells,
            width,
            height,
            row_offset: 0,
        }
    }

    // Shift all rows up by the specified amount (discard top rows, add None rows at bottom)
    // Uses circular buffer: just adjust offset and clear the newly available rows
    fn shift_up(&mut self, rows: usize) {
        let shift_amount = rows.min(self.height);

        // Clear the rows that will become the new bottom rows
        for i in 0..shift_amount {
            let physical_row = (self.row_offset + i) % self.height;
            for cell in 0..self.width {
                self.cells[physical_row][cell] = CellState::None;
            }
        }

        // Update offset to point to new logical start (circular)
        self.row_offset = (self.row_offset + shift_amount) % self.height;
    }

    // Get physical row index from logical row index
    #[inline]
    fn physical_row(&self, logical_row: usize) -> usize {
        (self.row_offset + logical_row) % self.height
    }
}

// ============================================================================
// Shared State & Synchronization
// ============================================================================

#[derive(Debug)]
enum SceneState {
    Presenting,
    Presented,
    NeedUpdate {
        reset: bool,
        scroll_left: bool,
        scroll_right: bool,
    },
    Updated(Arc<wgpu::Texture>),
    Exit,
}

struct SharedState {
    work_cv: Arc<(Mutex<SceneState>, Condvar)>,
    gif_path: Option<String>,
    gif_frame_skip: usize,
}

impl SharedState {
    fn new(gif_path: Option<String>, gif_frame_skip: usize) -> Self {
        SharedState {
            work_cv: Arc::new((Mutex::new(SceneState::Presented), Condvar::new())),
            gif_path,
            gif_frame_skip,
        }
    }
}

// State for GIF encoding thread
enum GifEncodeState {
    Idle,
    HasBuffer(Arc<wgpu::Buffer>),
    Encoding,
    Exit,
}

struct GifSharedState {
    cv: Arc<(Mutex<GifEncodeState>, Condvar)>,
    device: Arc<wgpu::Device>,
}

// ============================================================================
// Rule 110 Implementation
// ============================================================================

// Rule 110 as per TLA+ spec UpdateCell:
// 1. (1,1,1) → 0
// 2. (?,0,1) → 1
// 3. OTHER → preserve state
// Note: Using cyclic boundaries - wraps around at edges
fn update_cell(board: &mut Board, step: usize, cell: usize) -> bool {
    let current_physical = board.physical_row(step);
    if step == 0 || board.cells[current_physical][cell] != CellState::None {
        return false;
    }

    let last_physical = board.physical_row(step - 1);
    let last_row = &board.cells[last_physical];

    // Cyclic boundaries: wrap around at edges
    let left_neighbor = if cell > 0 {
        last_row[cell - 1]
    } else {
        last_row[board.width - 1]
    };

    let right_neighbor = if cell + 1 < board.width {
        last_row[cell + 1]
    } else {
        last_row[0]
    };

    let old_state = last_row[cell];

    // Check if neighbors are computed
    if left_neighbor == CellState::None || right_neighbor == CellState::None {
        return false;
    }

    // Rule 110 as per TLA+ spec:
    // 1. old_state = 1 /\ left_neighbor = 1 /\ right_neighbor = 1 -> 0
    // 2. old_state = 0 /\ right_neighbor = 1 -> 1
    // 3. OTHER -> last_row[cell]
    let new_state = if old_state == CellState::One
        && left_neighbor == CellState::One
        && right_neighbor == CellState::One
    {
        CellState::Zero
    } else if old_state == CellState::Zero && right_neighbor == CellState::One {
        CellState::One
    } else {
        old_state
    };

    board.cells[current_physical][cell] = new_state;
    true
}

// ============================================================================
// Renderer Threads
// ============================================================================

// GIF encoder thread
fn gif_encoder(gif_path: String, gif_shared: Arc<GifSharedState>) {
    let file = File::create(&gif_path).expect("failed to create GIF file");
    let writer = BufWriter::new(file);
    let mut encoder = GifEncoder::new(writer, WINDOW_WIDTH as u16, WINDOW_HEIGHT as u16, &[])
        .expect("failed to create GIF encoder");
    encoder
        .set_repeat(Repeat::Infinite)
        .expect("failed to set repeat");

    loop {
        let buffer = {
            let (lock, cvar) = &*gif_shared.cv;
            let mut state = lock.lock().unwrap();
            loop {
                match &*state {
                    GifEncodeState::HasBuffer(_) => break,
                    GifEncodeState::Exit => return,
                    GifEncodeState::Idle => {
                        state = cvar.wait(state).unwrap();
                    }
                    GifEncodeState::Encoding => {
                        unreachable!("Encoder should not be in Encoding state at loop start")
                    }
                }
            }
            // Take the buffer and transition to Encoding
            match std::mem::replace(&mut *state, GifEncodeState::Encoding) {
                GifEncodeState::HasBuffer(buffer) => buffer,
                _ => unreachable!(),
            }
        };

        // Map the buffer and copy data (this is the blocking part, now in encoder thread)
        let frame_data = {
            let buffer_slice = buffer.slice(..);
            let (tx, rx) = std::sync::mpsc::channel();
            buffer_slice.map_async(wgpu::MapMode::Read, move |result| {
                let _ = tx.send(result);
            });
            let _ = gif_shared.device.poll(wgpu::PollType::Wait);
            if rx.recv().unwrap().is_err() {
                eprintln!("Failed to map GIF capture buffer");
                // Transition back to Idle
                let (lock, _cvar) = &*gif_shared.cv;
                let mut state = lock.lock().unwrap();
                *state = GifEncodeState::Idle;
                continue;
            }
            let data = buffer_slice.get_mapped_range();
            let frame_data = data.to_vec();
            drop(data);
            buffer.unmap();
            frame_data
        };

        // Convert RGBA to indexed color
        let mut indexed = vec![0u8; (WINDOW_WIDTH * WINDOW_HEIGHT) as usize];
        let mut palette = vec![0u8; 256 * 3];

        // Create grayscale palette
        for i in 0..256 {
            palette[i * 3] = i as u8;
            palette[i * 3 + 1] = i as u8;
            palette[i * 3 + 2] = i as u8;
        }

        // Convert RGBA to grayscale index
        for i in 0..(WINDOW_WIDTH * WINDOW_HEIGHT) as usize {
            let r = frame_data[i * 4];
            let g = frame_data[i * 4 + 1];
            let b = frame_data[i * 4 + 2];
            let gray = ((r as u32 + g as u32 + b as u32) / 3) as u8;
            indexed[i] = gray;
        }

        let mut frame =
            Frame::from_indexed_pixels(WINDOW_WIDTH as u16, WINDOW_HEIGHT as u16, indexed, None);
        frame.palette = Some(palette);
        frame.delay = 6;

        if let Err(e) = encoder.write_frame(&frame) {
            eprintln!("Failed to write GIF frame: {}", e);
        }

        // Transition back to Idle
        {
            let (lock, _cvar) = &*gif_shared.cv;
            let mut state = lock.lock().unwrap();
            *state = GifEncodeState::Idle;
        }
    }
}

fn renderer(
    shared: Arc<SharedState>,
    proxy: EventLoopProxy<UserEvent>,
    device: Arc<wgpu::Device>,
    queue: Arc<wgpu::Queue>,
    gif_path: Option<String>,
    scroll_step: usize,
) {
    // Renderer owns the board - no sharing needed
    let mut board = Board::new(BOARD_WIDTH, BOARD_HEIGHT);
    let mut current_step = 1; // Start at step 1
    let mut frame_counter = 0; // Counter for GIF frame recording
    let mut viewport_offset = BOARD_WIDTH - VISIBLE_BOARD_WIDTH; // Start at rightmost position

    let mut renderer = Renderer::new(
        &*device,
        RendererOptions {
            antialiasing_support: AaSupport::area_only(),
            ..Default::default()
        },
    )
    .expect("failed to create renderer");

    let mut scene = Scene::new();

    // Two textures for double buffering: one being presented, one being rendered to
    let mut presenting: Option<Arc<wgpu::Texture>> = None;
    let mut rendering: Option<Arc<wgpu::Texture>> = None;

    // Start GIF encoder thread if recording
    let (gif_shared, gif_encoder_handle) = if let Some(path) = gif_path.as_ref() {
        let gif_shared = Arc::new(GifSharedState {
            cv: Arc::new((Mutex::new(GifEncodeState::Idle), Condvar::new())),
            device: Arc::clone(&device),
        });
        let gif_shared_clone = Arc::clone(&gif_shared);
        let path_clone = path.clone();
        let handle = thread::Builder::new()
            .name("gif_encoder".to_string())
            .spawn(move || {
                gif_encoder(path_clone, gif_shared_clone);
            })
            .expect("failed to spawn gif encoder thread");
        (Some(gif_shared), Some(handle))
    } else {
        (None, None)
    };

    loop {
        // Check if board is complete - if so, scroll it down by shifting up
        if current_step >= board.height {
            // Shift board up by STEPS_PER_FRAME rows (discard top rows, continue evolution at bottom)
            board.shift_up(STEPS_PER_FRAME);

            // Continue computing from where we left off (accounting for the shift)
            current_step = board.height - STEPS_PER_FRAME;
            // Fall through to compute the new rows immediately
        }

        // Compute next STEPS_PER_FRAME steps
        let end_step = (current_step + STEPS_PER_FRAME).min(board.height);

        for step in current_step..end_step {
            for cell in 0..board.width {
                update_cell(&mut board, step, cell);
            }
        }

        // Update current step
        current_step = end_step;

        // Clear scene and rebuild eagerly (parallel with main thread presenting)
        scene.reset();

        // Calculate offsets: viewport_offset determines horizontal position
        let start_col = viewport_offset;
        let end_col = (viewport_offset + VISIBLE_BOARD_WIDTH).min(board.width);
        let start_row = 0;
        let end_row = VISIBLE_BOARD_HEIGHT.min(current_step);

        // Draw the visible portion
        for row_idx in start_row..end_row {
            if row_idx >= board.height {
                break;
            }
            let physical_row = board.physical_row(row_idx);
            for col_idx in start_col..end_col {
                if col_idx >= board.width {
                    break;
                }
                let cell = board.cells[physical_row][col_idx];
                // Render at screen coordinates (not board coordinates)
                let x = (col_idx - start_col) as f64 * CELL_SIZE;
                let y = (row_idx - start_row) as f64 * CELL_SIZE;
                let rect = RoundedRect::new(x, y, x + CELL_SIZE, y + CELL_SIZE, 0.0);
                scene.fill(
                    vello::peniko::Fill::NonZero,
                    vello::kurbo::Affine::IDENTITY,
                    cell.color(),
                    None,
                    &rect,
                );
            }
        }

        // Render scene to texture
        // Get or create the texture that's not being presented
        let texture = rendering.get_or_insert_with(|| {
            Arc::new(device.create_texture(&wgpu::TextureDescriptor {
                label: Some("render_texture"),
                size: wgpu::Extent3d {
                    width: WINDOW_WIDTH,
                    height: WINDOW_HEIGHT,
                    depth_or_array_layers: 1,
                },
                mip_level_count: 1,
                sample_count: 1,
                dimension: wgpu::TextureDimension::D2,
                format: wgpu::TextureFormat::Rgba8Unorm,
                usage: wgpu::TextureUsages::RENDER_ATTACHMENT
                    | wgpu::TextureUsages::TEXTURE_BINDING
                    | wgpu::TextureUsages::STORAGE_BINDING
                    | wgpu::TextureUsages::COPY_SRC,
                view_formats: &[],
            }))
        });

        let texture_view = texture.create_view(&wgpu::TextureViewDescriptor::default());

        renderer
            .render_to_texture(
                &*device,
                &*queue,
                &scene,
                &texture_view,
                &vello::RenderParams {
                    base_color: Color::WHITE,
                    width: WINDOW_WIDTH,
                    height: WINDOW_HEIGHT,
                    antialiasing_method: AaConfig::Area,
                },
            )
            .expect("failed to render to texture");

        // Wait for NeedUpdate state
        {
            let (lock, cvar) = &*shared.work_cv;
            let mut state = lock.lock().unwrap();
            loop {
                match *state {
                    SceneState::NeedUpdate {
                        reset,
                        scroll_left,
                        scroll_right,
                    } => {
                        // If reset flag is true, reset the board and counters
                        if reset {
                            board = Board::new(BOARD_WIDTH, BOARD_HEIGHT);
                            current_step = 1;
                            frame_counter = 0;
                            viewport_offset = BOARD_WIDTH - VISIBLE_BOARD_WIDTH;
                        }
                        // Handle scrolling
                        if scroll_left && viewport_offset > 0 {
                            viewport_offset = viewport_offset.saturating_sub(scroll_step);
                        }
                        if scroll_right && viewport_offset + VISIBLE_BOARD_WIDTH < board.width {
                            viewport_offset = (viewport_offset + scroll_step)
                                .min(board.width - VISIBLE_BOARD_WIDTH);
                        }
                        // Swap the textures: rendering becomes presenting, presenting becomes rendering
                        std::mem::swap(&mut presenting, &mut rendering);
                        // Clone the Arc (not the texture) and send it
                        *state = SceneState::Updated(presenting.clone().unwrap());
                        break;
                    }
                    SceneState::Exit => {
                        // Signal GIF encoder thread to exit and join it
                        if let Some(gif_shared) = &gif_shared {
                            let (lock, cvar) = &*gif_shared.cv;
                            let mut state = lock.lock().unwrap();
                            *state = GifEncodeState::Exit;
                            cvar.notify_one();
                            drop(state);
                        }
                        drop(state);
                        if let Some(handle) = gif_encoder_handle {
                            let _ = handle.join();
                        }
                        return; // Exit renderer thread
                    }
                    _ => {
                        state = cvar.wait(state).unwrap();
                    }
                }
            }
        }
        let _ = proxy.send_event(UserEvent::RenderComplete);

        // Capture frame to GIF if recording (every Nth frame)
        if let Some(ref gif_shared) = gif_shared {
            frame_counter += 1;

            // Check if we should capture this frame
            let should_capture = frame_counter % shared.gif_frame_skip == 0;

            // Check if encoder is idle
            let encoder_is_idle = {
                let (lock, _cvar) = &*gif_shared.cv;
                let state = lock.lock().unwrap();
                matches!(*state, GifEncodeState::Idle)
            };

            if should_capture && encoder_is_idle {
                // Get the texture that was just rendered
                let texture_to_capture = presenting
                    .as_ref()
                    .expect("presenting texture should exist");

                // Create buffer to read texture data
                let buffer_size = (WINDOW_WIDTH * WINDOW_HEIGHT * 4) as wgpu::BufferAddress;
                let buffer = device.create_buffer(&wgpu::BufferDescriptor {
                    label: Some("capture_buffer"),
                    size: buffer_size,
                    usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
                    mapped_at_creation: false,
                });

                let mut copy_encoder =
                    device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
                        label: Some("capture_encoder"),
                    });

                // Copy texture to buffer using correct wgpu 26.0.1 API
                copy_encoder.copy_texture_to_buffer(
                    texture_to_capture.as_image_copy(),
                    wgpu::TexelCopyBufferInfo {
                        buffer: &buffer,
                        layout: wgpu::TexelCopyBufferLayout {
                            offset: 0,
                            bytes_per_row: Some(WINDOW_WIDTH * 4),
                            rows_per_image: None,
                        },
                    },
                    wgpu::Extent3d {
                        width: WINDOW_WIDTH,
                        height: WINDOW_HEIGHT,
                        depth_or_array_layers: 1,
                    },
                );

                queue.submit(std::iter::once(copy_encoder.finish()));

                // Send buffer to encoder thread (non-blocking, encoder will map it)
                {
                    let (lock, cvar) = &*gif_shared.cv;
                    let mut state = lock.lock().unwrap();
                    *state = GifEncodeState::HasBuffer(Arc::new(buffer));
                    cvar.notify_one();
                }
            } else if should_capture && !encoder_is_idle {
                // Encoder is busy, skip this frame
                eprintln!("Skipping GIF frame {} - encoder busy", frame_counter);
            }
        }
    }
}

// ============================================================================
// Event Types
// ============================================================================

enum UserEvent {
    RenderComplete,
}

// ============================================================================
// Application State & Event Handling
// ============================================================================

struct App {
    shared: Arc<SharedState>,
    proxy: EventLoopProxy<UserEvent>,
    scroll_step: usize,
    window: Option<Arc<Window>>,
    device: Option<Arc<wgpu::Device>>,
    queue: Option<Arc<wgpu::Queue>>,
    surface: Option<wgpu::Surface<'static>>,
    surface_config: Option<wgpu::SurfaceConfiguration>,
    blitter: Option<TextureBlitter>,
    paused: bool,
    need_reset: bool,
    need_scroll_left: bool,
    need_scroll_right: bool,
    renderer_handle: Option<thread::JoinHandle<()>>,
}

impl App {
    fn new(shared: Arc<SharedState>, proxy: EventLoopProxy<UserEvent>, scroll_step: usize) -> Self {
        App {
            shared,
            proxy,
            scroll_step,
            window: None,
            device: None,
            queue: None,
            surface: None,
            surface_config: None,
            blitter: None,
            paused: false, // Start running (pause when space pressed)
            need_reset: false,
            need_scroll_left: false,
            need_scroll_right: false,
            renderer_handle: None,
        }
    }
}

impl ApplicationHandler<UserEvent> for App {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        if self.window.is_some() {
            return;
        }

        let window_attrs = Window::default_attributes()
            .with_title("Cellular Automata Visualizer")
            .with_inner_size(winit::dpi::PhysicalSize::new(WINDOW_WIDTH, WINDOW_HEIGHT));

        let window = Arc::new(
            event_loop
                .create_window(window_attrs)
                .expect("failed to create window"),
        );

        // Initialize wgpu
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor {
            backends: wgpu::Backends::PRIMARY,
            ..Default::default()
        });

        let surface = instance
            .create_surface(window.clone())
            .expect("failed to create surface");

        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: Some(&surface),
            force_fallback_adapter: false,
        }))
        .expect("failed to get adapter");

        let (device, queue) = pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor {
            label: Some("main_device"),
            required_features: wgpu::Features::default(),
            required_limits: wgpu::Limits::default(),
            memory_hints: wgpu::MemoryHints::default(),
            trace: wgpu::Trace::Off,
        }))
        .expect("failed to get device");

        let device = Arc::new(device);
        let queue = Arc::new(queue);

        let size = window.inner_size();
        let surface_caps = surface.get_capabilities(&adapter);
        let surface_format = surface_caps
            .formats
            .iter()
            .find(|f| f.is_srgb())
            .copied()
            .unwrap_or(surface_caps.formats[0]);

        let config = wgpu::SurfaceConfiguration {
            usage: wgpu::TextureUsages::RENDER_ATTACHMENT,
            format: surface_format,
            width: size.width,
            height: size.height,
            present_mode: wgpu::PresentMode::AutoVsync,
            alpha_mode: surface_caps.alpha_modes[0],
            view_formats: vec![],
            desired_maximum_frame_latency: 2,
        };
        surface.configure(&device, &config);

        // Create TextureBlitter (takes only device and format)
        let blitter = TextureBlitter::new(&device, surface_format);

        // Start renderer thread
        let renderer_shared = Arc::clone(&self.shared);
        let renderer_proxy = self.proxy.clone();
        let renderer_device = Arc::clone(&device);
        let renderer_queue = Arc::clone(&queue);
        let gif_path = self.shared.gif_path.clone();
        let scroll_step = self.scroll_step;
        let handle = thread::Builder::new()
            .name("renderer".to_string())
            .spawn(move || {
                renderer(
                    renderer_shared,
                    renderer_proxy,
                    renderer_device,
                    renderer_queue,
                    gif_path,
                    scroll_step,
                );
            })
            .expect("failed to spawn renderer thread");
        self.renderer_handle = Some(handle);

        self.window = Some(window);
        self.device = Some(device);
        self.queue = Some(queue);
        self.surface = Some(surface);
        self.surface_config = Some(config);
        self.blitter = Some(blitter);

        // Start rendering immediately since we begin running
        if let Some(window) = &self.window {
            window.request_redraw();
        }
    }

    fn window_event(
        &mut self,
        event_loop: &ActiveEventLoop,
        _window_id: WindowId,
        event: WindowEvent,
    ) {
        if event_loop.exiting() {
            return;
        }

        match event {
            WindowEvent::CloseRequested => {
                // Signal renderer to exit
                let (lock, cvar) = &*self.shared.work_cv;
                let mut state = lock.lock().unwrap();
                *state = SceneState::Exit;
                cvar.notify_one();
                drop(state);

                event_loop.exit();
            }
            WindowEvent::RedrawRequested => {
                // Trigger renderer to compute next frame if not paused
                if !self.paused {
                    let (lock, cvar) = &*self.shared.work_cv;
                    let mut state = lock.lock().unwrap();
                    // State should be Presented when RedrawRequested is called
                    match *state {
                        SceneState::Presented => {
                            // Use the local flags and then clear them
                            let reset = self.need_reset;
                            let scroll_left = self.need_scroll_left;
                            let scroll_right = self.need_scroll_right;
                            self.need_reset = false;
                            self.need_scroll_left = false;
                            self.need_scroll_right = false;
                            *state = SceneState::NeedUpdate {
                                reset,
                                scroll_left,
                                scroll_right,
                            };
                            cvar.notify_one();
                        }
                        _ => {
                            // Missed a frame - renderer is still busy
                            eprintln!(
                                "Warning: Missed frame, renderer still in state: {:?}",
                                *state
                            );
                        }
                    }
                }
            }
            WindowEvent::KeyboardInput {
                event:
                    KeyEvent {
                        logical_key: Key::Named(NamedKey::Space),
                        state,
                        ..
                    },
                ..
            } => {
                // Space bar: pause while pressed
                let should_pause = state == ElementState::Pressed;
                let was_paused = self.paused;
                self.paused = should_pause;

                if was_paused && !should_pause {
                    // Just unpaused (space released): request redraw to start the cycle again
                    if let Some(window) = &self.window {
                        window.request_redraw();
                    }
                }
            }
            WindowEvent::KeyboardInput {
                event:
                    KeyEvent {
                        logical_key: Key::Named(NamedKey::Escape),
                        state: ElementState::Pressed,
                        ..
                    },
                ..
            } => {
                // Escape: set reset flag (will be applied on next redraw)
                self.need_reset = true;
            }
            WindowEvent::KeyboardInput {
                event:
                    KeyEvent {
                        logical_key: Key::Named(NamedKey::ArrowLeft),
                        state: ElementState::Pressed,
                        ..
                    },
                ..
            } => {
                // Arrow Left: scroll viewport left
                self.need_scroll_left = true;
            }
            WindowEvent::KeyboardInput {
                event:
                    KeyEvent {
                        logical_key: Key::Named(NamedKey::ArrowRight),
                        state: ElementState::Pressed,
                        ..
                    },
                ..
            } => {
                // Arrow Right: scroll viewport right
                self.need_scroll_right = true;
            }
            WindowEvent::Resized(size) => {
                if let (Some(surface), Some(device), Some(config)) =
                    (&self.surface, &self.device, &mut self.surface_config)
                {
                    config.width = size.width;
                    config.height = size.height;
                    surface.configure(device, config);
                }
            }
            _ => {}
        }
    }

    fn user_event(&mut self, event_loop: &ActiveEventLoop, event: UserEvent) {
        if event_loop.exiting() {
            return;
        }

        match event {
            UserEvent::RenderComplete => {
                // Blit texture to surface and present
                if let Some(window) = &self.window {
                    window.pre_present_notify();

                    if let (Some(blitter), Some(surface), Some(device), Some(queue)) =
                        (&self.blitter, &self.surface, &self.device, &self.queue)
                    {
                        // Take the texture and transition to Presenting
                        let texture = {
                            let (lock, _cvar) = &*self.shared.work_cv;
                            let mut state = lock.lock().unwrap();

                            if let SceneState::Updated(texture) =
                                std::mem::replace(&mut *state, SceneState::Presenting)
                            {
                                texture
                            } else {
                                panic!("Expected Updated state in RenderComplete");
                            }
                        };

                        // Now blit without holding the lock
                        let surface_texture = surface
                            .get_current_texture()
                            .expect("failed to get surface texture");

                        let mut encoder =
                            device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
                                label: Some("copy_encoder"),
                            });

                        let texture_view =
                            texture.create_view(&wgpu::TextureViewDescriptor::default());
                        let surface_view = surface_texture
                            .texture
                            .create_view(&wgpu::TextureViewDescriptor::default());

                        blitter.copy(&device, &mut encoder, &texture_view, &surface_view);

                        queue.submit(std::iter::once(encoder.finish()));
                        surface_texture.present();

                        // Signal renderer that presentation is done
                        {
                            let (lock, cvar) = &*self.shared.work_cv;
                            let mut state = lock.lock().unwrap();
                            *state = SceneState::Presented;
                            cvar.notify_one();
                        }
                    }
                }

                // Request next frame if not paused
                if !self.paused {
                    if let Some(window) = &self.window {
                        window.request_redraw();
                    }
                }
            }
        }
    }

    fn exiting(&mut self, _event_loop: &ActiveEventLoop) {
        // Join renderer thread on exit
        if let Some(handle) = self.renderer_handle.take() {
            let _ = handle.join();
        }
    }
}

fn main() {
    let args = Args::parse();

    let shared = Arc::new(SharedState::new(args.record_gif, args.gif_frame_skip));

    // Create event loop
    let event_loop = EventLoop::<UserEvent>::with_user_event()
        .build()
        .expect("failed to create event loop");
    event_loop.set_control_flow(ControlFlow::Wait);

    let proxy = event_loop.create_proxy();

    // Renderer thread will be started in resumed()
    let mut app = App::new(shared, proxy, args.scroll_step);

    event_loop
        .run_app(&mut app)
        .expect("failed to run event loop");
}
