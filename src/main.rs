use rayon::prelude::*;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use vello::kurbo::RoundedRect;
use vello::peniko::Color;
use vello::util::{RenderContext, RenderSurface};
use vello::{AaConfig, AaSupport, Renderer, RendererOptions, Scene};
use winit::application::ApplicationHandler;
use winit::event::{ElementState, KeyEvent, WindowEvent};
use winit::event_loop::{ActiveEventLoop, ControlFlow, EventLoop, EventLoopProxy};
use winit::keyboard::{Key, NamedKey};
use winit::window::{Window, WindowId};

const CELL_SIZE: f64 = 4.0;
const WINDOW_WIDTH: u32 = 1600;
const WINDOW_HEIGHT: u32 = 1200;
const BOARD_WIDTH: usize = (WINDOW_WIDTH as f64 / CELL_SIZE) as usize;
const BOARD_HEIGHT: usize = (WINDOW_HEIGHT as f64 / CELL_SIZE) as usize;
const NUM_THREADS: usize = 4;

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
            CellState::None => Color::rgb8(220, 220, 220), // Light grey
        }
    }
}

#[derive(Clone)]
struct Board {
    cells: Vec<Vec<CellState>>,
    width: usize,
    height: usize,
}

impl Board {
    fn new(width: usize, height: usize) -> Self {
        let mut cells = vec![vec![CellState::None; width]; height];
        // Init: starting with a single rightmost black cell in the first row
        cells[0] = (0..width)
            .map(|cell| {
                if cell < width - 1 {
                    CellState::Zero
                } else {
                    CellState::One
                }
            })
            .collect();

        Board {
            cells,
            width,
            height,
        }
    }

    fn is_complete(&self) -> bool {
        self.cells
            .iter()
            .all(|row| row.iter().all(|&cell| cell != CellState::None))
    }

    fn reset_with_last_row(&mut self) {
        let last_row = self.cells[self.height - 1].clone();
        self.cells = vec![vec![CellState::None; self.width]; self.height];
        self.cells[0] = last_row;
    }
}

struct SharedState {
    board: Arc<Mutex<Board>>,
    paused: Arc<Mutex<bool>>,
    compute_cv: Arc<(Mutex<bool>, Condvar)>,
    render_cv: Arc<(Mutex<bool>, Condvar)>,
    board_complete: Arc<Mutex<bool>>,
}

impl SharedState {
    fn new(width: usize, height: usize) -> Self {
        SharedState {
            board: Arc::new(Mutex::new(Board::new(width, height))),
            paused: Arc::new(Mutex::new(true)),
            compute_cv: Arc::new((Mutex::new(false), Condvar::new())),
            render_cv: Arc::new((Mutex::new(false), Condvar::new())),
            board_complete: Arc::new(Mutex::new(false)),
        }
    }
}

// UpdateCell implementation following the TLA+ spec
fn update_cell(
    board: &mut Board,
    step: usize,
    cell: usize,
) -> bool {
    if step == 0 || board.cells[step][cell] != CellState::None {
        return false;
    }

    let last_row = &board.cells[step - 1];

    let left_neighbor = if cell > 0 {
        last_row[cell - 1]
    } else {
        CellState::Zero
    };

    let right_neighbor = if cell + 1 < board.width {
        last_row[cell + 1]
    } else {
        CellState::Zero
    };

    let old_state = last_row[cell];

    // Check if neighbors are computed
    if left_neighbor == CellState::None || right_neighbor == CellState::None {
        return false;
    }

    // Rule 110 logic from TLA+ spec
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

    board.cells[step][cell] = new_state;
    true
}

fn compute_worker(shared: Arc<SharedState>) {
    loop {
        // Wait for signal to start computing
        {
            let (lock, cvar) = &*shared.compute_cv;
            let mut should_compute = lock.lock().unwrap();
            while !*should_compute {
                should_compute = cvar.wait(should_compute).unwrap();
            }
            *should_compute = false;
        }

        // Check if paused
        let paused = *shared.paused.lock().unwrap();
        if paused {
            continue;
        }

        // Perform computation
        let mut board = shared.board.lock().unwrap();

        // Update cells from right to left, row by row
        for step in 1..board.height {
            let row_width = board.width;

            // Split the row into chunks for parallel processing
            let chunk_size = (row_width + NUM_THREADS - 1) / NUM_THREADS;
            let chunks: Vec<usize> = (0..NUM_THREADS)
                .map(|i| {
                    let start = i * chunk_size;
                    if start >= row_width {
                        0
                    } else {
                        std::cmp::min(chunk_size, row_width - start)
                    }
                })
                .collect();

            // Process chunks in parallel
            // We need to be careful with the shared board access
            // For simplicity, we'll process each row sequentially but cells in parallel
            let cells_to_update: Vec<usize> = (0..row_width).rev().collect();

            // Split cells into chunks
            let mut chunk_starts = vec![];
            let mut pos = 0;
            for &chunk_len in &chunks {
                if chunk_len > 0 {
                    chunk_starts.push(pos);
                    pos += chunk_len;
                }
            }

            // For parallel processing, we need to drop the lock and use Arc<Mutex<Board>>
            // But this is complex, so let's use a simpler approach:
            // Process right to left, allowing parallelism within chunks
            drop(board);

            for chunk_idx in 0..chunk_starts.len() {
                let start_pos = chunk_starts[chunk_idx];
                let chunk_len = chunks[chunk_idx];
                let end_pos = start_pos + chunk_len;

                // Process this chunk's cells from right to left in parallel
                let chunk_cells: Vec<usize> = cells_to_update[start_pos..end_pos].to_vec();

                // Lock board for each chunk
                let board_arc = Arc::clone(&shared.board);

                chunk_cells.par_iter().for_each(|&cell| {
                    let mut board = board_arc.lock().unwrap();
                    update_cell(&mut board, step, cell);
                });
            }

            board = shared.board.lock().unwrap();
        }

        // Check if board is complete
        if board.is_complete() {
            *shared.board_complete.lock().unwrap() = true;
        }
    }
}

fn render_worker(shared: Arc<SharedState>, proxy: EventLoopProxy<UserEvent>) {
    loop {
        // Wait for signal to start rendering
        {
            let (lock, cvar) = &*shared.render_cv;
            let mut should_render = lock.lock().unwrap();
            while !*should_render {
                should_render = cvar.wait(should_render).unwrap();
            }
            *should_render = false;
        }

        // Build the scene
        let mut scene = Scene::new();
        {
            let board = shared.board.lock().unwrap();
            for (row_idx, row) in board.cells.iter().enumerate() {
                for (col_idx, &cell) in row.iter().enumerate() {
                    let x = col_idx as f64 * CELL_SIZE;
                    let y = row_idx as f64 * CELL_SIZE;
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
        }

        // Notify main thread that rendering is ready
        let _ = proxy.send_event(UserEvent::RenderComplete(scene));
    }
}

enum UserEvent {
    RenderComplete(Scene),
}

struct App {
    shared: Arc<SharedState>,
    window: Option<Arc<Window>>,
    render_cx: Option<RenderContext>,
    render_surface: Option<RenderSurface<'static>>,
    renderer: Option<Renderer>,
    scene: Option<Scene>,
}

impl App {
    fn new(shared: Arc<SharedState>) -> Self {
        App {
            shared,
            window: None,
            render_cx: None,
            render_surface: None,
            renderer: None,
            scene: None,
        }
    }

    fn handle_render_complete(&mut self, scene: Scene) {
        self.scene = Some(scene);
        if let Some(window) = &self.window {
            window.pre_present_notify();
            
            // Present the frame
            if let (Some(renderer), Some(surface), Some(render_cx), Some(scene)) = (
                &mut self.renderer,
                &mut self.render_surface,
                &self.render_cx,
                &self.scene,
            ) {
                let device = &render_cx.devices[surface.dev_id].device;
                let queue = &render_cx.devices[surface.dev_id].queue;
                
                let width = surface.config.width;
                let height = surface.config.height;
                let surface_texture = surface
                    .surface
                    .get_current_texture()
                    .expect("failed to get surface texture");

                renderer
                    .render_to_surface(
                        device,
                        queue,
                        scene,
                        &surface_texture,
                        &vello::RenderParams {
                            base_color: Color::WHITE,
                            width,
                            height,
                            antialiasing_method: AaConfig::Area,
                        },
                    )
                    .expect("failed to render to surface");

                surface_texture.present();
            }

            // Check if board is complete
            if *self.shared.board_complete.lock().unwrap() {
                // Reset board with last row
                let mut board = self.shared.board.lock().unwrap();
                board.reset_with_last_row();
                *self.shared.board_complete.lock().unwrap() = false;
            }

            // Request next frame if not paused
            let paused = *self.shared.paused.lock().unwrap();
            if !paused {
                window.request_redraw();
            }
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

        // Initialize render context
        let mut render_cx = RenderContext::new();
        let size = window.inner_size();
        let render_surface = pollster::block_on(
            render_cx.create_surface(
                window.clone(),
                size.width,
                size.height,
                wgpu::PresentMode::AutoVsync,
            ),
        )
        .expect("failed to create surface");

        let device = &render_cx.devices[render_surface.dev_id].device;

        let renderer = Renderer::new(
            device,
            RendererOptions {
                surface_format: Some(render_surface.format),
                use_cpu: false,
                antialiasing_support: AaSupport::area_only(),
                num_init_threads: None,
            },
        )
        .expect("failed to create renderer");

        self.window = Some(window);
        self.render_cx = Some(render_cx);
        self.render_surface = Some(render_surface);
        self.renderer = Some(renderer);
    }

    fn window_event(
        &mut self,
        event_loop: &ActiveEventLoop,
        _window_id: WindowId,
        event: WindowEvent,
    ) {
        match event {
            WindowEvent::CloseRequested => {
                event_loop.exit();
            }
            WindowEvent::KeyboardInput {
                event:
                    KeyEvent {
                        logical_key: Key::Named(NamedKey::Space),
                        state: ElementState::Pressed,
                        ..
                    },
                ..
            } => {
                // Toggle pause state
                let mut paused = self.shared.paused.lock().unwrap();
                *paused = !*paused;
                let new_paused = *paused;
                drop(paused);

                if !new_paused {
                    // Unpause: request redraw
                    if let Some(window) = &self.window {
                        window.request_redraw();
                    }
                }
            }
            WindowEvent::RedrawRequested => {
                // Notify compute thread to wait
                // Notify render thread to start
                {
                    let (lock, cvar) = &*self.shared.render_cv;
                    let mut should_render = lock.lock().unwrap();
                    *should_render = true;
                    cvar.notify_one();
                }
            }
            WindowEvent::Resized(size) => {
                if let (Some(render_cx), Some(render_surface)) =
                    (&mut self.render_cx, &mut self.render_surface)
                {
                    render_cx.resize_surface(render_surface, size.width, size.height);
                }
            }
            _ => {}
        }
    }

    fn user_event(&mut self, _event_loop: &ActiveEventLoop, event: UserEvent) {
        match event {
            UserEvent::RenderComplete(scene) => {
                self.handle_render_complete(scene);
                
                // Notify compute thread to continue
                let paused = *self.shared.paused.lock().unwrap();
                if !paused {
                    let (lock, cvar) = &*self.shared.compute_cv;
                    let mut should_compute = lock.lock().unwrap();
                    *should_compute = true;
                    cvar.notify_one();
                }
            }
        }
    }
}

fn main() {
    let shared = Arc::new(SharedState::new(BOARD_WIDTH, BOARD_HEIGHT));

    // Start compute thread
    let compute_shared = Arc::clone(&shared);
    thread::spawn(move || {
        compute_worker(compute_shared);
    });

    // Create event loop
    let event_loop = EventLoop::<UserEvent>::with_user_event()
        .build()
        .expect("failed to create event loop");
    event_loop.set_control_flow(ControlFlow::Wait);

    let proxy = event_loop.create_proxy();

    // Start render thread
    let render_shared = Arc::clone(&shared);
    thread::spawn(move || {
        render_worker(render_shared, proxy);
    });

    // Run application
    let mut app = App::new(shared);
    event_loop.run_app(&mut app).expect("failed to run event loop");
}
