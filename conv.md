# Rule 110 Cellular Automaton Visualizer - Evolution

## Project Requirements

> **gterzian**: Goal of the project: 2d visualizer of history of 1d automaton.
> 
> Requirements:
> - Use TLA+ spec for automata algorithm
> - Use Vello for drawing
> - Use rayon for thread-pool
> - Use winit for window management
> 
> Important: follow the TLA spec closely to implement the automata logic.

## Understanding TLA+ Specification

### Rule 110 Correctness Verification

Initially misunderstood the TLA+ spec as "incomplete" when seeing unexpected patterns. After careful analysis and correction from the user, realized the spec is actually a beautifully minimal encoding that captures exactly when states change.

The TLA+ spec defines Rule 110 with elegant minimalism:

```tlaplus
new_state == CASE old_state = 1 /\ left_neighbor = 1 /\ right_neighbor = 1 -> 0
              []  old_state = 0 /\ right_neighbor = 1 -> 1
              [] OTHER -> last_row[cell]
```

**Key insight**: The spec is not simplified - it's a correct encoding that captures exactly when states change:
1. The only time a `1` becomes `0` is pattern 111
2. The only time a `0` becomes `1` is when the right neighbor is 1
3. Everything else preserves its state

This correctly implements all 8 patterns of Rule 110 (binary: 01101110).

## Architecture Evolution

### Simplifications

User decided to simplify the initial design:
- **Parallel computation → Single-threaded**: Removed column-based parallelization with multiple worker threads competing for shared board state. Simplified to single worker thread with exclusive board ownership.
- **Dependencies pruned**: Removed rayon (no longer needed), later re-added clap for CLI args

### Key Bug Fixes
1. **Pause/unpause synchronization**: Fixed condvar notification timing
2. **Compute loop**: Worker was immediately setting flags that broke processing
3. **Race condition in state machine**: Added `Presenting` state to prevent worker from consuming `NeedUpdate` prematurely

### Infinite Scrolling
> **gterzian**: Instead of stopping at `Done`: keep "scrolling down" by popping a compute step from the top of the board, and pushing a compute step to the bottom.

User updated the TLA+ spec to support infinite evolution instead of stopping when the board fills. Implementation should be a refinement of the spec - maintaining all invariants while creating an infinite scrolling view.

Implemented circular buffer with `row_offset` for O(1) scrolling. When board fills, shifts by `STEPS_PER_FRAME` (10 rows) to match compute granularity. Initial attempt shifted by 1 row; user corrected to shift by the full compute step size for smoother scrolling.

## State Machine Evolution

### Initial: Scene-Based
- `NeedUpdate(scene)` - Scene ready for worker
- `ComputingUpdate` - Worker computing
- `Updated(scene)` - Scene ready to render

### After Vello 0.6 + Render-to-Texture
- `Presenting` - Main thread blitting, worker must wait
- `NeedUpdate` - Ready for worker to compute
- `ComputingUpdate` - Worker computing
- `Updated(texture)` - Texture ready to blit
- `Exit` - Signal worker to terminate

**Key change**: Worker now renders to texture, main thread uses `TextureBlitter` to blit to surface.

## Vello 0.6 Migration

User requested updating to latest vello (0.6.0) and moving render-to-texture to the worker thread, with main thread using TextureBlitter to blit to surface. This architecture change required updating wgpu and handling API differences.

Updated dependencies:
- vello 0.3 → 0.6.0
- wgpu 22 → 26.0.1

**API changes**:
- `Color::rgb8()` → `Color::from_rgb8()`
- `render_to_texture()` takes `&TextureView` instead of `&Texture`
- Explicit `AaSupport` required

**Architecture**: Worker renders scene to texture, main thread blits to surface. Single device/queue Arc-shared between threads.

## GIF Recording Feature

**gterzian**: "Add a command line option to save the run to a gif file, and implement it using https://docs.rs/gif/latest/gif/"

User required security audit before adding any new dependencies. Vendored the gif crate and all dependencies, reviewed source code for unsafe operations and security issues.

### Security Audit
Vendored and audited gif crate v0.13.3:
- Uses `#![forbid(unsafe_code)]`
- Maintained by image-rs team
- Proper error handling
- **Verdict: SAFE TO USE**

### Architecture Evolution

### Non-Blocking Architecture Refactoring

User identified that buffer mapping was blocking the worker thread on GPU operations, which was undesirable. Requested moving the blocking operations to a dedicated encoder thread, with state-based frame skipping when the encoder is busy. Multiple iterations to get the architecture right: first moved capture to worker, then created dedicated encoder thread, then moved buffer mapping to encoder thread.

**Initial**: Frame capture in worker with blocking buffer mapping.

**Problem**: GPU blocking in worker thread during buffer mapping.

**Solution**: Three-thread system with dedicated encoder thread.

### Three-Thread Architecture
1. **Main thread**: Event loop, texture blitting, presentation
2. **Worker thread**: Computation, scene building, rendering, frame capture coordination
3. **GIF encoder thread**: Buffer mapping (blocking operation), RGBA→grayscale conversion, GIF encoding

### GifEncodeState Machine
Variants ordered by occurrence:
- `Idle` - Encoder ready to receive frame
- `HasBuffer(Arc<wgpu::Buffer>)` - Buffer ready to process
- `Encoding` - Processing frame (unreachable in wait loop)
- `Exit` - Terminal state

### Non-Blocking Frame Capture Flow
1. Worker checks if encoder is `Idle` (skip frame if busy)
2. Worker creates buffer and submits GPU copy command (non-blocking)
3. Worker sends `Arc<wgpu::Buffer>` to encoder thread
4. Encoder maps buffer (blocking, isolated to encoder thread)
5. Encoder converts RGBA→grayscale and writes GIF frame (6/100s delay)
6. Encoder transitions back to `Idle`

### wgpu 26.0.1 API Compatibility

Initial implementation used incorrect type names from older wgpu versions, causing compilation errors. Multiple failed attempts with different type combinations. User provided link to Servo's vello_backend.rs as a working reference for the correct wgpu 26.0.1 API patterns.

Used Servo's vello_backend.rs as reference for correct API:
- `wgpu::TexelCopyBufferInfo` (not `ImageCopyBuffer`)
- `wgpu::TexelCopyBufferLayout` (not `ImageDataLayout`)
- `wgpu::PollType::Poll`/`::Wait` (not `Maintain` enum)

### Thread Cleanup
Hierarchical shutdown:
1. Worker detects `SceneState::Exit`
2. Worker signals encoder with `GifEncodeState::Exit`
3. Worker joins encoder thread handle
4. Clean termination

### Code Quality
- Removed unnecessary print statements (kept diagnostic warnings)
- Made state machine invariant explicit: `Encoding` is `unreachable!()` in encoder's wait loop
- Ordered enum variants by actual state flow

## Architecture Summary

**Current system**:
- **Three threads**: Main (event loop + blitting), worker (compute + render), encoder (GIF writing)
- **Render-to-texture**: Worker renders to wgpu texture, main thread blits to surface
- **Shared device/queue**: Arc-wrapped, shared between threads
- **Circular buffer**: O(1) board scrolling using row_offset
- **State machines**: `SceneState` (5 variants), `GifEncodeState` (4 variants)
- **Non-blocking**: Worker never blocks on GPU operations
- **Frame skipping**: Graceful handling when encoder busy
- **Board layout**: 3x wider than visible (1200×300), renders middle third (400×300)
- **Cyclic boundaries**: Wrapping at edges per TLA+ spec
- **Infinite scrolling**: Shifts by 10 rows when full
- **Clean shutdown**: Exit states propagate, threads join properly

**Dependencies**:
- vello 0.6.0 - 2D rendering
- wgpu 26.0.1 - GPU API
- winit - Window management
- gif 0.13.3 - GIF encoding
- clap 4.5 - CLI parsing

**Event flow**:
```
SPACE pressed → request redraw
RedrawRequested → set NeedUpdate + notify worker
Worker computes → renders to texture → Updated(texture) + RenderComplete
RenderComplete → take texture + set Presenting + blit to surface + present
Loop continues via next RedrawRequested
```
