## Rule 110 Cellular Automaton Visualizer

Displays the evolution of a 1D [Rule 110](https://mathworld.wolfram.com/Rule110.html) cellular automaton as a 2D history.

TLA+ [spec](Rule_110.tla) written by hand; code generated as a result of a conversation [summarized here](conversation_summary.md) for technical highlights and evolution of the implementation.

Supporting blog post: [TLA+ in support of AI code generation](https://medium.com/@polyglot_factotum/tla-in-support-of-ai-code-generation-9086fc9715c4)

### Features

- Interactive visualization with pause/unpause controls
- System runs automatically and pauses while SPACE is held down
- Release SPACE to resume computation and rendering (10 rows per frame)
- Board starts with a single black cell at the top-right and evolves via Rule 110
- Infinite scrolling - board shifts upward when full to continue evolution
- Uses cyclic boundaries (wrapping at edges)
- Optional GIF recording with configurable frame skip

### Build and Run

Requirements:
- Rust toolchain (stable)
- GPU with [wgpu](https://github.com/gfx-rs/wgpu) support (see [platform support](https://github.com/gfx-rs/wgpu?tab=readme-ov-file#supported-platforms))

```bash
# Build the project
cargo build --release

# Run the visualizer
cargo run --release

# Run with GIF recording (default: record every 10th frame)
cargo run --release -- --record-gif output.gif

# Run with GIF recording every frame (slower, larger file)
cargo run --release -- --record-gif output.gif --gif-frame-skip 1

# Run with GIF recording every 30th frame (faster, smaller file)
cargo run --release -- --record-gif output.gif --gif-frame-skip 30
```

### Command-Line Arguments

- `--record-gif <FILE>`: Optional path to save the visualization as a GIF file. When enabled, frames are captured and encoded in a separate thread without blocking the main visualization.
- `--gif-frame-skip <N>`: Record every Nth frame to GIF (default: 10). Lower values create smoother but larger GIFs; higher values create smaller files but skip more frames.

### Example Output

Below is a sample GIF of Rule 110 evolution starting from a single cell:

![Rule 110 Visualization](output.gif)
