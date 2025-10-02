mod app;
mod automata;
mod compute;
mod matrix;
mod render;
mod types;

use app::App;
use clap::Parser;
use compute::spawn_compute_thread;
use matrix::Matrix;
use std::sync::Arc;
use types::ComputeShared;
use winit::event_loop::EventLoop;

#[derive(Parser, Debug)]
#[command(name = "automata")]
#[command(about = "1D Cellular Automata Visualizer (Rule 110)", long_about = None)]
struct Args {
    #[arg(long, default_value_t = 400)]
    width: usize,

    #[arg(long, default_value_t = 300)]
    height: usize,

    #[arg(long, default_value_t = 4)]
    threads: usize,
}

fn main() {
    let args = Args::parse();

    let matrix = Arc::new(Matrix::new(args.width, args.height, args.threads));
    let compute_shared = ComputeShared::new();

    let event_loop = EventLoop::new().unwrap();

    let _compute_handle =
        spawn_compute_thread(matrix.clone(), compute_shared.clone(), args.threads);

    let mut app = App::new(
        matrix.clone(),
        compute_shared.clone(),
        args.width,
        args.height,
    );

    event_loop.run_app(&mut app).unwrap();
}
