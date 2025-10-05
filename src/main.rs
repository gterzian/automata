// Rule 110 Cellular Automaton Visualizer
//
// Displays the evolution of a 1D Rule 110 cellular automaton as a 2D history.
// - Press and hold SPACE to compute and render (10 rows per frame)
// - Release SPACE to pause
// - Board starts with a random row and evolves infinitely
// - When the board fills up, it scrolls down (shifts up) and continues computing

use rand::Rng;
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
const VISIBLE_BOARD_WIDTH: usize = (WINDOW_WIDTH as f64 / CELL_SIZE) as usize;
const VISIBLE_BOARD_HEIGHT: usize = (WINDOW_HEIGHT as f64 / CELL_SIZE) as usize;
// Compute board 3x wider than visible area (but same height)
const BOARD_WIDTH: usize = VISIBLE_BOARD_WIDTH * 3;
const BOARD_HEIGHT: usize = VISIBLE_BOARD_HEIGHT;
const STEPS_PER_FRAME: usize = 10; // Rows computed per frame

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
    row_offset: usize, // Circular buffer offset: logical row 0 maps to cells[row_offset]
}

impl Board {
    fn new(width: usize, height: usize) -> Self {
        let mut cells = vec![vec![CellState::None; width]; height];
        let mut rng = rand::thread_rng();

        // Init: starting with random 0s and 1s in the first row (as per spec)
        cells[0] = (0..width)
            .map(|_| {
                if rng.gen::<bool>() {
                    CellState::One
                } else {
                    CellState::Zero
                }
            })
            .collect();

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

struct SharedState {
    board: Arc<Mutex<Board>>,
    work_cv: Arc<(Mutex<bool>, Condvar)>,
    current_step: Arc<Mutex<usize>>, // Current row being computed
}

impl SharedState {
    fn new(width: usize, height: usize) -> Self {
        SharedState {
            board: Arc::new(Mutex::new(Board::new(width, height))),
            work_cv: Arc::new((Mutex::new(false), Condvar::new())),
            current_step: Arc::new(Mutex::new(1)), // Start at step 1
        }
    }
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
// Worker Threads
// ============================================================================

fn worker(shared: Arc<SharedState>, proxy: EventLoopProxy<UserEvent>) {
    // Reuse scene across frames to avoid allocations
    let mut scene = Scene::new();

    loop {
        // Wait for signal to start work
        {
            let (lock, cvar) = &*shared.work_cv;
            let mut should_work = lock.lock().unwrap();
            while !*should_work {
                should_work = cvar.wait(should_work).unwrap();
            }
            *should_work = false;
        }

        // Get current step and board dimensions
        let mut current_step = *shared.current_step.lock().unwrap();
        let (_board_width, board_height) = {
            let board = shared.board.lock().unwrap();
            (board.width, board.height)
        };

        // Check if board is complete - if so, scroll it down by shifting up
        if current_step >= board_height {
            // Shift board up by STEPS_PER_FRAME rows (discard top rows, continue evolution at bottom)
            let mut board = shared.board.lock().unwrap();
            board.shift_up(STEPS_PER_FRAME);
            drop(board);

            // Continue computing from where we left off (accounting for the shift)
            *shared.current_step.lock().unwrap() = board_height - STEPS_PER_FRAME;

            // Update current_step for the computation below
            current_step = board_height - STEPS_PER_FRAME;
            // Fall through to compute the new rows immediately
        }

        // Compute next STEPS_PER_FRAME steps
        let mut board = shared.board.lock().unwrap();
        let end_step = (current_step + STEPS_PER_FRAME).min(board.height);

        for step in current_step..end_step {
            for cell in 0..board.width {
                update_cell(&mut board, step, cell);
            }
        }

        // Update current step
        *shared.current_step.lock().unwrap() = end_step;
        let current = end_step;

        // Clear scene from previous frame and rebuild
        scene.reset();

        // Calculate offsets: middle third horizontally, but from top vertically
        let start_col = VISIBLE_BOARD_WIDTH;
        let end_col = start_col + VISIBLE_BOARD_WIDTH;
        let start_row = 0;
        let end_row = VISIBLE_BOARD_HEIGHT.min(current);

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
        drop(board);

        // Notify main thread with the scene to render
        // Note: We need to clone the scene since we're retaining it for reuse
        let _ = proxy.send_event(UserEvent::RenderComplete(scene.clone()));
    }
}

// ============================================================================
// Event Types
// ============================================================================

enum UserEvent {
    RenderComplete(Scene),
}

// ============================================================================
// Application State & Event Handling
// ============================================================================

struct App {
    shared: Arc<SharedState>,
    proxy: EventLoopProxy<UserEvent>,
    window: Option<Arc<Window>>,
    render_cx: Option<RenderContext>,
    render_surface: Option<RenderSurface<'static>>,
    renderer: Option<Renderer>,
    paused: bool,
    worker_handle: Option<thread::JoinHandle<()>>,
}

impl App {
    fn new(shared: Arc<SharedState>, proxy: EventLoopProxy<UserEvent>) -> Self {
        App {
            shared,
            proxy,
            window: None,
            render_cx: None,
            render_surface: None,
            renderer: None,
            paused: false, // Start unpaused
            worker_handle: None,
        }
    }

    fn request_compute_and_redraw(&self) {
        // Signal worker thread
        let (lock, cvar) = &*self.shared.work_cv;
        *lock.lock().unwrap() = true;
        cvar.notify_one();
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
        let render_surface = pollster::block_on(render_cx.create_surface(
            window.clone(),
            size.width,
            size.height,
            wgpu::PresentMode::AutoVsync,
        ))
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

        // Start worker thread (merged compute + render)
        let worker_shared = Arc::clone(&self.shared);
        let worker_proxy = self.proxy.clone();
        let handle = thread::Builder::new()
            .name("worker".to_string())
            .spawn(move || {
                worker(worker_shared, worker_proxy);
            })
            .expect("failed to spawn worker thread");
        self.worker_handle = Some(handle);

        self.window = Some(window.clone());
        self.render_cx = Some(render_cx);
        self.render_surface = Some(render_surface);
        self.renderer = Some(renderer);

        // Start rendering immediately since we begin unpaused
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
        match event {
            WindowEvent::CloseRequested => {
                event_loop.exit();
            }
            WindowEvent::RedrawRequested => {
                // Signal worker to compute and build scene when we need a frame
                if !self.paused {
                    self.request_compute_and_redraw();
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
                // Space bar: work only while pressed
                let should_work = state == ElementState::Pressed;
                let was_paused = self.paused;
                self.paused = !should_work;

                if was_paused && should_work {
                    // Just unpaused: request compute and redraw
                    self.request_compute_and_redraw();
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
                // Render scene to surface and present
                if let Some(window) = &self.window {
                    window.pre_present_notify();

                    if let (Some(renderer), Some(surface), Some(render_cx)) = (
                        &mut self.renderer,
                        &mut self.render_surface,
                        &self.render_cx,
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
                                &scene,
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
}

fn main() {
    let shared = Arc::new(SharedState::new(BOARD_WIDTH, BOARD_HEIGHT));

    // Create event loop
    let event_loop = EventLoop::<UserEvent>::with_user_event()
        .build()
        .expect("failed to create event loop");
    event_loop.set_control_flow(ControlFlow::Wait);

    let proxy = event_loop.create_proxy();

    // Worker thread will be started in resumed()
    let mut app = App::new(shared, proxy);

    event_loop
        .run_app(&mut app)
        .expect("failed to run event loop");

    // Note: Worker threads are infinite loops, so they won't naturally exit.
    // In a real application, you'd want to add shutdown signaling.
    // For now, the OS will clean them up when the process exits.
}
