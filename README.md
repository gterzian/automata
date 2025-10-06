## Rule 110 Cellular Automaton Visualizer

Displays the evolution of a 1D [Rule 110](https://mathworld.wolfram.com/Rule110.html) cellular automaton as a 2D history.

TLA+ [spec](spec.tla) written by hand; code generated as a result of a conversation [summarized here](conversation_summary.md) for technical highlights and evolution of the implementation.

Supporting blog post: [TLA+ in support of AI code generation](https://medium.com/@polyglot_factotum/tla-in-support-of-ai-code-generation-9086fc9715c4)

### Features

- Interactive visualization with pause/unpause controls
- Press and hold SPACE to compute and render (10 rows per frame)
- Release SPACE to pause
- Board starts with random row and scrolls infinitely
- Uses cyclic boundaries (wrapping at edges)
- Optional GIF recording of the visualization

### Build and Run

Requirements:
- Rust toolchain (stable)
- GPU with [wgpu](https://github.com/gfx-rs/wgpu) support (see [platform support](https://github.com/gfx-rs/wgpu?tab=readme-ov-file#supported-platforms))

```bash
# Build the project
cargo build --release

# Run the visualizer
cargo run --release

# Run with GIF recording
cargo run --release -- --record-gif output.gif
```

### Command-Line Arguments

- `--record-gif <FILE>`: Optional path to save the visualization as a GIF file. When enabled, frames are captured and encoded in a separate thread without blocking the main visualization.

### Example Output

![Rule 110 Visualization](output.gif)
