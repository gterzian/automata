// Rule 110 Cellular Automaton Visualizer
//
// Displays the evolution of a 1D Rule 110 cellular automaton as a 2D history.
// - Press and hold SPACE to compute and render (10 rows per frame)
// - Release SPACE to pause
// - Each board starts with a random seed pattern
// - Automatically restarts with new random seed when board is complete

use rand::Rng;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Instant;
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

    fn new_with_random_seed(width: usize, height: usize, seed_length: usize) -> Self {
        let mut cells = vec![vec![CellState::None; width]; height];
        let mut rng = rand::thread_rng();

        let actual_seed_length = seed_length.min(width);
        let start_pos = width - actual_seed_length;

        // White padding on left
        for i in 0..start_pos {
            cells[0][i] = CellState::Zero;
        }

        // Random seed on the right
        for i in start_pos..width {
            cells[0][i] = if rng.gen::<bool>() {
                CellState::One
            } else {
                CellState::Zero
            };
        }

        Board {
            cells,
            width,
            height,
        }
    }
}

// ============================================================================
// Shared State & Synchronization
// ============================================================================

struct SharedState {
    board: Arc<Mutex<Board>>,
    next_board: Arc<Mutex<Option<Board>>>, // Next board for transition
    transition_progress: Arc<Mutex<f64>>,  // 0.0 = show board, 1.0 = show next_board
    transition_start: Arc<Mutex<Option<Instant>>>, // When transition started
    paused: Arc<Mutex<bool>>,
    compute_cv: Arc<(Mutex<bool>, Condvar)>,
    render_cv: Arc<(Mutex<bool>, Condvar)>,
    seed_length: Arc<Mutex<usize>>, // Length of the seed pattern to take
    current_step: Arc<Mutex<usize>>, // Current row being computed
}

impl SharedState {
    fn new(width: usize, height: usize) -> Self {
        SharedState {
            board: Arc::new(Mutex::new(Board::new(width, height))),
            next_board: Arc::new(Mutex::new(None)),
            transition_progress: Arc::new(Mutex::new(0.0)),
            transition_start: Arc::new(Mutex::new(None)),
            paused: Arc::new(Mutex::new(true)),
            compute_cv: Arc::new((Mutex::new(false), Condvar::new())),
            render_cv: Arc::new((Mutex::new(false), Condvar::new())),
            seed_length: Arc::new(Mutex::new(1)), // Start with 1 cell seed
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
fn update_cell(board: &mut Board, step: usize, cell: usize) -> bool {
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

fn compute_worker(shared: Arc<SharedState>, proxy: EventLoopProxy<UserEvent>) {
    loop {
        // Wait for signal to start computing
        {
            let (lock, cvar) = &*shared.compute_cv;
            let mut should_compute = lock.lock().unwrap();
            while !*should_compute {
                should_compute = cvar.wait(should_compute).unwrap();
            }
            *should_compute = false; // Reset flag after starting
        }

        // Check if paused
        let paused = *shared.paused.lock().unwrap();
        if paused {
            continue;
        }

        // Get current step and board height
        let current_step = *shared.current_step.lock().unwrap();
        let board_height = shared.board.lock().unwrap().height;

        // Check if board is complete
        if current_step >= board_height {
            // Board is complete, prepare for transition
            let computed_board = shared.board.lock().unwrap().clone();

            *shared.next_board.lock().unwrap() = Some(computed_board);
            *shared.transition_start.lock().unwrap() = Some(Instant::now());
            *shared.transition_progress.lock().unwrap() = 0.0;

            // Notify main thread that computation is complete
            let _ = proxy.send_event(UserEvent::ComputeComplete);
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

        // Notify main thread to render
        let _ = proxy.send_event(UserEvent::StepComplete);
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

        // Get current transition progress
        let progress = *shared.transition_progress.lock().unwrap();

        // Build the scene - use interpolation to blend colors more efficiently
        let scene = {
            let board = shared.board.lock().unwrap();
            let next_board = shared.next_board.lock().unwrap();

            let mut scene = Scene::new();

            // Helper to linearly interpolate between two colors
            let lerp_color = |c1: Color, c2: Color, t: f64| -> Color {
                let t = t.clamp(0.0, 1.0);
                Color::rgb(
                    c1.r as f64 / 255.0 * (1.0 - t) + c2.r as f64 / 255.0 * t,
                    c1.g as f64 / 255.0 * (1.0 - t) + c2.g as f64 / 255.0 * t,
                    c1.b as f64 / 255.0 * (1.0 - t) + c2.b as f64 / 255.0 * t,
                )
            };

            // Draw cells with interpolated colors
            if let Some(ref next) = *next_board {
                for (row_idx, (curr_row, next_row)) in
                    board.cells.iter().zip(next.cells.iter()).enumerate()
                {
                    for (col_idx, (&curr_cell, &next_cell)) in
                        curr_row.iter().zip(next_row.iter()).enumerate()
                    {
                        let x = col_idx as f64 * CELL_SIZE;
                        let y = row_idx as f64 * CELL_SIZE;
                        let rect = RoundedRect::new(x, y, x + CELL_SIZE, y + CELL_SIZE, 0.0);

                        let color = lerp_color(curr_cell.color(), next_cell.color(), progress);

                        scene.fill(
                            vello::peniko::Fill::NonZero,
                            vello::kurbo::Affine::IDENTITY,
                            color,
                            None,
                            &rect,
                        );
                    }
                }
            } else {
                // No transition, just draw current board
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

            scene
        };

        // Determine if transition is complete
        let is_complete = progress >= 1.0;

        // Send the built scene to the main thread
        let render_type = if is_complete {
            RenderType::Final(scene)
        } else {
            RenderType::Transition(scene)
        };
        let _ = proxy.send_event(UserEvent::RenderComplete(render_type));
    }
}

// ============================================================================
// Event Types
// ============================================================================

enum RenderType {
    Transition(Scene), // Intermediate frame during transition
    Final(Scene),      // Final frame, transition complete
}

enum UserEvent {
    ComputeComplete,
    StepComplete,
    RenderComplete(RenderType),
}

// ============================================================================
// Application State & Event Handling
// ============================================================================

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

    fn seed_next_board_and_continue(&mut self) {
        // Lock the board to get dimensions
        let board_width = {
            let board = self.shared.board.lock().unwrap();
            board.width
        };

        // Generate a random seed length (somewhere between 10 and full width)
        let mut rng = rand::thread_rng();
        let new_seed_length = rng.gen_range(10..=board_width);

        // Reset seed length tracker and current step
        *self.shared.seed_length.lock().unwrap() = new_seed_length;
        *self.shared.current_step.lock().unwrap() = 1; // Reset to step 1

        // Create a new board with a random seed
        let new_board = Board::new_with_random_seed(board_width, BOARD_HEIGHT, new_seed_length);

        // Update shared state
        *self.shared.board.lock().unwrap() = new_board;

        // Signal compute thread to continue
        {
            let (lock, cvar) = &*self.shared.compute_cv;
            let mut should_compute = lock.lock().unwrap();
            *should_compute = true;
            cvar.notify_one();
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
            WindowEvent::RedrawRequested => {
                // Present the current scene when redraw is requested
                if let Some(scene) = self.scene.clone() {
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
                let mut paused = self.shared.paused.lock().unwrap();
                let was_paused = *paused;
                *paused = !should_work;
                drop(paused);

                if was_paused && should_work {
                    // Just started: signal compute to start
                    {
                        let (lock, cvar) = &*self.shared.compute_cv;
                        let mut should_compute = lock.lock().unwrap();
                        *should_compute = true;
                        cvar.notify_one();
                    }
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
            UserEvent::StepComplete => {
                // Render current state
                {
                    let (lock, cvar) = &*self.shared.render_cv;
                    let mut should_render = lock.lock().unwrap();
                    *should_render = true;
                    cvar.notify_one();
                }

                // Continue computing if not paused
                let paused = *self.shared.paused.lock().unwrap();
                if !paused {
                    let (lock, cvar) = &*self.shared.compute_cv;
                    let mut should_compute = lock.lock().unwrap();
                    *should_compute = true;
                    cvar.notify_one();
                }
            }
            UserEvent::ComputeComplete => {
                // Set progress to 1.0 for instant transition
                *self.shared.transition_progress.lock().unwrap() = 1.0;

                // Signal render thread to render the final frame
                {
                    let (lock, cvar) = &*self.shared.render_cv;
                    let mut should_render = lock.lock().unwrap();
                    *should_render = true;
                    cvar.notify_one();
                }
            }
            UserEvent::RenderComplete(render_type) => {
                match render_type {
                    RenderType::Transition(scene) => {
                        // Progressive rendering: just display current state
                        self.scene = Some(scene);

                        if let Some(window) = &self.window {
                            window.request_redraw();
                        }
                    }
                    RenderType::Final(scene) => {
                        // Store the final scene
                        self.scene = Some(scene);

                        // Request window redraw to present it
                        if let Some(window) = &self.window {
                            window.request_redraw();
                        }

                        // Transition complete, swap boards
                        if let Some(next) = self.shared.next_board.lock().unwrap().take() {
                            *self.shared.board.lock().unwrap() = next;
                        }
                        *self.shared.transition_start.lock().unwrap() = None;
                        *self.shared.transition_progress.lock().unwrap() = 0.0;

                        // Now seed the next board and signal compute to continue
                        let paused = *self.shared.paused.lock().unwrap();
                        if !paused {
                            self.seed_next_board_and_continue();
                        }
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

    // Start compute thread
    let compute_shared = Arc::clone(&shared);
    let compute_proxy = proxy.clone();
    thread::spawn(move || {
        compute_worker(compute_shared, compute_proxy);
    });

    // Start render thread
    let render_shared = Arc::clone(&shared);
    let render_proxy = proxy.clone();
    thread::spawn(move || {
        render_worker(render_shared, render_proxy);
    });

    // Run application
    let mut app = App::new(shared);
    event_loop
        .run_app(&mut app)
        .expect("failed to run event loop");
}
