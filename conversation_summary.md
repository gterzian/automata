# Rule 110 Cellular Automaton Visualizer - Evolution

## Original Request

> **gterzian**: Goal of the project: 2d visualizer of history of 1d automaton.
> 
> Requirements:
> - Use TLA+ spec for automata algorithm
> - Use Vello for drawing
> - Use rayon for thread-pool
> - Use winit for window management
> 
> Notes on compute: update cells from right to left per row, and break-up rows in conceptual columns to be computed in parallel by 4 threads. To enable this, the entire matrix should be shared in a arc + mutex, so should individual rows, and individuals chunks of rows. The idea is that there should be minimal contention on the cells which two workers need to read/write, since by the time a worker compute the left most cell in a column/chunk, the worker computing the neighboring chunk will have moved on further to the left.
> 
> Notes on render: try to do as much as possible using vello in the background thread(scene building, but also is possible render to offscreen buffer), and then back on the main thread do what it necessary to update the screen.
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

**gterzian**: "Don't always just listen to me, there is a bug in the setting of should compute to new paused"

Fixed condvar notification timing - was notifying unnecessarily when pausing.

**gterzian**: "At the beginning of the compute worker loop, there is a bug based on the logic we added. Make sure you try to prevent these kind of side effects"

Fixed critical bug where worker was immediately setting `should_compute = false` after waking up, breaking the processing loop.

**gterzian**: "Add another variant to the state enum: Presenting..."

Added `Presenting` state to fix race condition where worker could consume `NeedUpdate` while main thread was between finishing blit and calling request_redraw.

### Infinite Scrolling
> **gterzian**: Instead of stopping at `Done`: keep "scrolling down" by popping a compute step from the top of the board, and pushing a compute step to the bottom.

User updated the TLA+ spec to support infinite evolution instead of stopping when the board fills. Implementation should be a refinement of the spec - maintaining all invariants while creating an infinite scrolling view.

Implemented circular buffer with `row_offset` for O(1) scrolling. When board fills, shifts by `STEPS_PER_FRAME` (10 rows) to match compute granularity. Initial attempt shifted by 1 row; user corrected to shift by the full compute step size for smoother scrolling.

## State Machine Evolution

### Episode 1: Initial Three-State Machine

**Initial problem**: Scene was being cloned on every frame. User suggested putting it in shared state.

**gterzian**: "do you need to clone the scene to send it to the main thread? Is that not something to add to the shared state instead?"

**gterzian**: "so put an `Option<Scene>` in `work_cv`, and use that to also replace the 'should work' boolean."

First attempt used `Option<Scene>` but had logic errors, leading to panics.

**gterzian**: "No so the problem is the worker goes back to the beginning of the loop and then takes the scene again, so if the render event is received you can't be sure the scene is some. We need to do more than use an option around the scene, rather we need an enum with three variants: NeedUpdate(scene), ComputingUpdate, Updated(scene)."

Implemented proper three-state machine:
- `NeedUpdate(scene)` - Scene ready for worker
- `ComputingUpdate` - Worker computing
- `Updated(scene)` - Scene ready to render

**gterzian**: "only start the compute when RedrawRequested comes in, and only if not paused. This means RenderComplete should just keep the lock and use the scene, not set it immediately to NeedUpdate. Also, we want to re-use the same scene (make sure to reset it)."

Corrected flow: trigger compute from RedrawRequested instead of RenderComplete.

### Episode 2: Race Condition Discovery - Adding Presenting State

After Vello 0.6 migration with render-to-texture, discovered a subtle race condition that caused occasional panics.

**gterzian**: "You're right that on start-up, if the worker sets the state to computing before redraw requested comes in, it will panic. But that doesn't happen often, I'm seeing a panic after a while only so far.

Ah I know what it is: in `RenderComplete`, main thread holds a lock, and only releases it at the end(actually it drops and re-aquires it). So the worker thread could be at the top of its loop, not waiting on the condvar but waiting on the lock, and then reading `NeedUpdate` and setting is to computing, meaning that at the next redraw event it is not in `NeedUpdate` anymore.

This is how to address it:
- Add another variant to the state enum: Presenting, and in `RenderComplete`, take the state out, and replace it with `Presenting`, and drop the lock.
- Initial state should be also `Presenting`.
- In `RedrawRequested`, assert it is `Presenting`, and set it to `NeedUpdate`, and then notify on the condvar."

**The problem**: While main thread held lock to blit, then dropped and reacquired it to set NeedUpdate, the worker could grab the lock in between and transition to ComputingUpdate before the next RedrawRequested.

**The solution**: Added `Presenting` state as a barrier:
- `Presenting` - Main thread is blitting/presenting, worker must wait
- `NeedUpdate` - Ready for worker to start computing
- `ComputingUpdate` - Worker is computing
- `Updated(texture)` - Texture ready to blit
- `Exit` - Signal worker to terminate

**Key insight**: `Presenting` prevents worker from transitioning NeedUpdate while main thread is between finishing a blit and calling request_redraw().

### Episode 3: GIF Recording - Similar Pattern in GifEncodeState

When implementing GIF recording, encountered similar coordination issues.

**gterzian**: "It's ok for the gif to miss frames, expected event, so add a `Encoding` variant to `GifEncodeState`, and only send a new frame if it is `Idle`."

Applied same state machine pattern to coordinate worker and encoder thread:
- `Idle` - Encoder ready to receive frame
- `HasBuffer(Arc<wgpu::Buffer>)` - Buffer ready to process
- `Encoding` - Processing frame
- `Exit` - Terminal state

Worker checks encoder state before capturing: only capture if `Idle`, skip frame if `Encoding`.

**gterzian**: "`GifEncodeState::Encoding` at the top of the encoder is unreachable(or should be)."

Made invariant explicit: encoder sets `Encoding` itself and transitions out before looping back, so it should be `unreachable!()` in the wait loop.

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

**gterzian**: "keep the join handle to the encoder, join on it when you exit"

**gterzian**: "Add a `Exit` variant to the surface. When `WindowEvent::CloseRequested`, set the surface state to it, and when the worker encounters that state, it breaks out of it's main loop(exits). In `ApplicationHandler::exiting`, you can then also join on the thread."

Implemented hierarchical shutdown:
1. Worker detects `SceneState::Exit`
2. Worker signals encoder with `GifEncodeState::Exit`
3. Worker joins encoder thread handle
4. Clean termination

### Code Quality

**gterzian**: "In the definition of an enum expressing a state machine like `GifEncodeState`, it's good practice for the variant to be, if possible, defined in the order in which they will occur in practice."

Reordered enum variants to match actual state flow (Idle → HasBuffer → Encoding → Idle, Exit).

**gterzian**: "remove prints(except the two re missed frame). `GifEncodeState::Encoding` at the top of the encoder is unreachable(or should be)."

Removed unnecessary print statements (kept diagnostic warnings). Made state machine invariant explicit: `Encoding` is `unreachable!()` in encoder's wait loop, enforcing that encoder should never be in `Encoding` state at loop start.

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
