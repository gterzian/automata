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
const BOARD_WIDTH: usize = (WINDOW_WIDTH as f64 / CELL_SIZE) as usize; // Full width
const BOARD_HEIGHT: usize = (WINDOW_HEIGHT as f64 / CELL_SIZE) as usize; // Full height

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
}

struct SharedState {
    board: Arc<Mutex<Board>>,
    paused: Arc<Mutex<bool>>,
    compute_cv: Arc<(Mutex<bool>, Condvar)>,
    render_cv: Arc<(Mutex<bool>, Condvar)>,
    seed_length: Arc<Mutex<usize>>, // Length of the seed pattern to take
    white_length: Arc<Mutex<usize>>, // Length of white padding (used after seed reaches full width)
}

impl SharedState {
    fn new(width: usize, height: usize) -> Self {
        SharedState {
            board: Arc::new(Mutex::new(Board::new(width, height))),
            paused: Arc::new(Mutex::new(true)),
            compute_cv: Arc::new((Mutex::new(false), Condvar::new())),
            render_cv: Arc::new((Mutex::new(false), Condvar::new())),
            seed_length: Arc::new(Mutex::new(1)), // Start with 1 cell seed
            white_length: Arc::new(Mutex::new(0)), // No white padding initially
        }
    }
}

// UpdateCell implementation following the TLA+ spec
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

        // Compute the entire board sequentially
        let mut board = shared.board.lock().unwrap();
        for step in 1..board.height {
            for cell in 0..board.width {
                update_cell(&mut board, step, cell);
            }
        }
        drop(board);

        // Notify main thread that computation is complete
        let _ = proxy.send_event(UserEvent::ComputeComplete);
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

        // Take a snapshot of the current board
        let board_snapshot = {
            let board = shared.board.lock().unwrap();
            board.clone()
        };

        // Note: We'll build the scene in the main thread after receiving this
        // Just send the board snapshot as part of the event
        let _ = proxy.send_event(UserEvent::RenderComplete(board_snapshot));
    }
}

enum UserEvent {
    ComputeComplete,
    RenderComplete(Board), // board_snapshot
}

struct App {
    shared: Arc<SharedState>,
    window: Option<Arc<Window>>,
    render_cx: Option<RenderContext>,
    render_surface: Option<RenderSurface<'static>>,
    renderer: Option<Renderer>,
    scene: Option<Scene>,
    current_board: Option<Board>, // Single full-screen board
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
            current_board: None,
        }
    }

    fn present_scene(&mut self, scene: Scene) {
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
        }
    }

    fn seed_next_board_and_continue(&mut self, completed_board: Board) {
        let board_width = completed_board.width;
        let bottom_row = &completed_board.cells[completed_board.height - 1];

        // Get current seed and white lengths
        let mut seed_len = self.shared.seed_length.lock().unwrap();
        let mut white_len = self.shared.white_length.lock().unwrap();

        let mut new_board = Board::new(completed_board.width, completed_board.height);
        let mut rng = rand::thread_rng();

        if *white_len == 0 {
            // Phase 1: Expand the seed from the right edge
            let old_seed_len = (*seed_len).min(board_width);

            // Grow by a random amount
            let growth = rng.gen_range(1..=10);
            let new_seed_len = (old_seed_len + growth).min(board_width);
            *seed_len = new_seed_len;

            let start_pos = board_width - new_seed_len;
            let old_start_pos = board_width - old_seed_len;

            // White padding on left
            for i in 0..start_pos {
                new_board.cells[0][i] = CellState::Zero;
            }

            // Copy the old seed from the previous bottom row
            let cells_to_copy = old_seed_len.min(board_width - (start_pos + growth));
            for i in 0..cells_to_copy {
                if start_pos + growth + i < board_width && old_start_pos + i < board_width {
                    new_board.cells[0][start_pos + growth + i] = bottom_row[old_start_pos + i];
                }
            }

            // Add new random cells to the left of the existing seed (growing leftward)
            for i in start_pos..(start_pos + growth).min(board_width) {
                new_board.cells[0][i] = if rng.gen::<bool>() {
                    CellState::One
                } else {
                    CellState::Zero
                };
            }

            if *seed_len >= board_width {
                *white_len = 1;
            }
        } else {
            // Phase 2: White cells expand from left, shrinking the seed on the right
            let old_white_len = *white_len;
            let growth = rng.gen_range(1..=10);
            let new_white_len = (old_white_len + growth).min(board_width);
            *white_len = new_white_len;

            // White cells on left
            for i in 0..new_white_len {
                new_board.cells[0][i] = CellState::Zero;
            }

            // Copy the remaining seed from the previous bottom row
            let random_portion = board_width.saturating_sub(new_white_len);

            // The seed shifts left as white expands
            for i in 0..random_portion {
                let source_idx = old_white_len + i + growth;
                if source_idx < board_width {
                    new_board.cells[0][new_white_len + i] = bottom_row[source_idx];
                } else {
                    // If we run out of source, fill with random
                    new_board.cells[0][new_white_len + i] = if rng.gen::<bool>() {
                        CellState::One
                    } else {
                        CellState::Zero
                    };
                }
            }

            if *white_len >= board_width {
                *seed_len = 1;
                *white_len = 0;
            }
        }

        drop(seed_len);
        drop(white_len);

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
                    // Unpause: signal compute to start
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
            UserEvent::ComputeComplete => {
                // Computation done, signal render thread to start
                {
                    let (lock, cvar) = &*self.shared.render_cv;
                    let mut should_render = lock.lock().unwrap();
                    *should_render = true;
                    cvar.notify_one();
                }
            }
            UserEvent::RenderComplete(board_snapshot) => {
                // Store the board
                self.current_board = Some(board_snapshot.clone());

                // Build scene with full screen board
                let mut scene = Scene::new();

                // Draw the full board
                for (row_idx, row) in board_snapshot.cells.iter().enumerate() {
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

                // Present the scene
                self.present_scene(scene);

                // Now seed the next board and signal compute to continue
                let paused = *self.shared.paused.lock().unwrap();
                if !paused {
                    self.seed_next_board_and_continue(board_snapshot);
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
