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
const BOARD_WIDTH: usize = (WINDOW_WIDTH as f64 / CELL_SIZE) as usize;
const BOARD_HEIGHT: usize = (WINDOW_HEIGHT as f64 / CELL_SIZE) as usize;
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
        }
    }

    // Shift all rows up by the specified amount (discard top rows, add None rows at bottom)
    fn shift_up(&mut self, rows: usize) {
        let shift_amount = rows.min(self.height);

        // Shift rows up
        for row in shift_amount..self.height {
            self.cells[row - shift_amount] = self.cells[row].clone();
        }

        // Add new empty rows at bottom
        for row in (self.height - shift_amount)..self.height {
            self.cells[row] = vec![CellState::None; self.width];
        }
    }
}

// ============================================================================
// Shared State & Synchronization
// ============================================================================

struct SharedState {
    board: Arc<Mutex<Board>>,
    compute_cv: Arc<(Mutex<bool>, Condvar)>,
    render_cv: Arc<(Mutex<bool>, Condvar)>,
    current_step: Arc<Mutex<usize>>, // Current row being computed
}

impl SharedState {
    fn new(width: usize, height: usize) -> Self {
        SharedState {
            board: Arc::new(Mutex::new(Board::new(width, height))),
            compute_cv: Arc::new((Mutex::new(false), Condvar::new())),
            render_cv: Arc::new((Mutex::new(false), Condvar::new())),
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
    if step == 0 || board.cells[step][cell] != CellState::None {
        return false;
    }

    let last_row = &board.cells[step - 1];

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

    board.cells[step][cell] = new_state;
    true
}

// ============================================================================
// Worker Threads
// ============================================================================

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

        // Get current step and board dimensions
        let current_step = *shared.current_step.lock().unwrap();
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

            // Don't compute yet, wait for next signal
            continue;
        }

        // Compute next STEPS_PER_FRAME steps
        let mut board = shared.board.lock().unwrap();
        let end_step = (current_step + STEPS_PER_FRAME).min(board.height);

        for step in current_step..end_step {
            for cell in 0..board.width {
                update_cell(&mut board, step, cell);
            }
        }
        drop(board);

        // Update current step
        *shared.current_step.lock().unwrap() = end_step;
    }
}

fn render_worker(
    shared: Arc<SharedState>,
    render_cv: Arc<(Mutex<bool>, Condvar)>,
    proxy: EventLoopProxy<UserEvent>,
) {
    loop {
        // Wait for signal to render
        {
            let (lock, cvar) = &*render_cv;
            let mut should_render = lock.lock().unwrap();
            while !*should_render {
                should_render = cvar.wait(should_render).unwrap();
            }
            *should_render = false;
        }

        // Build scene from current board state
        let scene = {
            let board = shared.board.lock().unwrap();
            let mut scene = Scene::new();

            // Draw cells
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

            scene
        };

        // Notify main thread with the scene to render
        let _ = proxy.send_event(UserEvent::RenderComplete(scene));
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
        }
    }

    fn request_compute_and_redraw(&self) {
        // Signal compute thread
        let (lock, cvar) = &*self.shared.compute_cv;
        *lock.lock().unwrap() = true;
        cvar.notify_one();
        // Request window redraw
        if let Some(window) = &self.window {
            window.request_redraw();
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

        // Start render thread
        let render_shared = Arc::clone(&self.shared);
        let render_cv = Arc::clone(&self.shared.render_cv);
        let proxy = self.proxy.clone();
        thread::spawn(move || {
            render_worker(render_shared, render_cv, proxy);
        });

        self.window = Some(window.clone());
        self.render_cx = Some(render_cx);
        self.render_surface = Some(render_surface);
        self.renderer = Some(renderer);

        // Start rendering immediately since we begin unpaused
        self.request_compute_and_redraw();
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
                // Ignore if paused
                if self.paused {
                    return;
                }

                // Signal render thread to build scene
                let (lock, cvar) = &*self.shared.render_cv;
                *lock.lock().unwrap() = true;
                cvar.notify_one();
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
                    self.request_compute_and_redraw();
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

    // Start compute thread
    let compute_shared = Arc::clone(&shared);
    thread::spawn(move || {
        compute_worker(compute_shared);
    });

    // Run application (render thread will be started in resumed())
    let mut app = App::new(shared, proxy);
    event_loop
        .run_app(&mut app)
        .expect("failed to run event loop");
}
