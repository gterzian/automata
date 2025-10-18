# Rule 110 Cellular Automaton Visualizer - Development History

## About This Document

This document chronicles the development of a Rule 110 cellular automaton visualizer, written from my perspective as GitHub Copilot—an AI programming assistant working alongside a human developer. It captures our collaborative process: the user's requirements and corrections, my implementations and misunderstandings, and the iterative refinements that shaped the final architecture. The narrative structure (Episodes 1-9) reflects how the codebase evolved through multiple sessions, with each episode documenting a specific problem, the user's guidance, and the resulting solution. This document serves as both a technical record and a learning artifact, showing how complex concurrent systems emerge through careful iteration and debugging.

## Project Goals

**Original Vision**: 2D visualizer showing the evolution history of a 1D cellular automaton.

**Initial Requirements**:
- Use TLA+ specification for automata algorithm correctness
- Vello for GPU-accelerated 2D rendering
- Rayon for parallel computation thread-pool
- Winit for window management
- Parallel computation: 4 threads processing conceptual columns of rows right-to-left
- Render offscreen in background thread, update display on main thread

**Important**: Follow TLA+ spec closely for correctness.

## Understanding Rule 110

### TLA+ Specification

Initially misunderstood the TLA+ spec as "incomplete" when seeing unexpected patterns. User corrected this misunderstanding - the spec is actually elegantly minimal, capturing exactly when states change:

```tlaplus
new_state == CASE old_state = 1 /\ left_neighbor = 1 /\ right_neighbor = 1 -> 0
              []  old_state = 0 /\ right_neighbor = 1 -> 1
              [] OTHER -> last_row[cell]
```

**Key insight**: This correctly implements all 8 patterns of Rule 110 (binary: 01101110):
1. Pattern 111 → 0 (only time a `1` becomes `0`)
2. Pattern ?01 → 1 (any state with right neighbor `1` becomes `1`)  
3. All other patterns preserve their state

## Vello 0.6 Migration

User requested updating to vello 0.6.0, moving render-to-texture to renderer thread, with main using `TextureBlitter`.

**Dependency updates**:
- vello 0.3 → 0.6.0
- wgpu 22 → 26.0.1

**API changes**:
- `Color::rgb8()` → `Color::from_rgb8()`
- `render_to_texture()` takes `&TextureView` instead of `&Texture`
- Explicit `AaSupport` required

**Architecture**: Renderer renders to texture, main blits to surface. Single device/queue Arc-shared between threads.

## Architecture Simplifications

User decided to simplify the initial parallel design:

**Changes**:
- **Parallel → Single-threaded**: Removed complex column-based parallelization with 4 threads competing for shared board state
- **Simplified ownership**: Single renderer thread owns the board exclusively
- **Dependencies**: Removed rayon (no longer needed), later added clap for CLI arguments

## Board Layout Evolution

The visible board layout evolved to give Rule 110 more space to develop complex patterns.

### 1x Layout: Full Board Visible
- Board: 400×300 cells = Window: 1600×1200 pixels (4px per cell)
- What you compute is what you see

### 3x Layout: Middle Third Visible  
- Board: 1200×300 cells (3x wider than window)
- Viewport: Middle third (cells 400-799)
- Rationale: Patterns evolve off-screen on left, mature in visible middle, dissipate on right

### 10x Layout: Leftmost Edge Visible
**User**: "So now I want to make the board ten times as wide, and, retaining the same window size, only render the left most side of it."

- Board: 4000×300 cells (10x wider than window)
- Viewport: Leftmost edge (cells 0-399)
- Rationale: Massive horizontal space for pattern formation, viewing the evolutionary "birth" region

This progression reflects understanding that Rule 110 is computationally universal and needs space to generate complex patterns.

### Infinite Scrolling

**User**: "Instead of stopping at `Done`: keep 'scrolling down' by popping a compute step from the top of the board, and pushing a compute step to the bottom."

User updated TLA+ spec to support infinite evolution. Implemented circular buffer with `row_offset` for O(1) scrolling. When board fills, shifts by `STEPS_PER_FRAME` (10 rows) to match compute granularity.

## Core Bug Fixes

### Condvar Notification Timing
**User**: "Don't always just listen to me, there is a bug in the setting of should compute to new paused"

Fixed: Was notifying unnecessarily when pausing.

### Loop Re-entry Bug
**User**: "At the beginning of the compute renderer loop, there is a bug based on the logic we added. Make sure you try to prevent these kind of side effects"

Fixed: Renderer was immediately setting `should_compute = false` after waking up, breaking the processing loop.

## State Machine Evolution

### Episode 1: From Option to Three-State Machine

**Problem**: Scene was being cloned on every frame.

**User**: "do you need to clone the scene to send it to the main thread? Is that not something to add to the shared state instead?"

**First attempt**: Used `Option<Scene>` but had logic errors.

**User**: "No so the problem is the renderer goes back to the beginning of the loop and then takes the scene again, so if the render event is received you can't be sure the scene is some. We need to do more than use an option around the scene, rather we need an enum with three variants: NeedUpdate(scene), ComputingUpdate, Updated(scene)."

**Solution**: Proper three-state machine:
- `NeedUpdate(scene)` - Scene ready for renderer
- `ComputingUpdate` - Renderer computing
- `Updated(scene)` - Scene ready to render

**User**: "only start the compute when RedrawRequested comes in, and only if not paused. This means RenderComplete should just keep the lock and use the scene, not set it immediately to NeedUpdate. Also, we want to re-use the same scene (make sure to reset it)."

Corrected flow: Trigger compute from `RedrawRequested` instead of `RenderComplete`.

### Episode 2: Adding Presenting State (Race Condition)

After Vello 0.6 migration with render-to-texture, discovered subtle race condition causing occasional panics.

**User**: "You're right that on start-up, if the renderer sets the state to computing before redraw requested comes in, it will panic. But that doesn't happen often, I'm seeing a panic after a while only so far.

Ah I know what it is: in `RenderComplete`, main thread holds a lock, and only releases it at the end(actually it drops and re-aquires it). So the renderer thread could be at the top of its loop, not waiting on the condvar but waiting on the lock, and then reading `NeedUpdate` and setting is to computing, meaning that at the next redraw event it is not in `NeedUpdate` anymore.

This is how to address it:
- Add another variant to the state enum: Presenting, and in `RenderComplete`, take the state out, and replace it with `Presenting`, and drop the lock.
- Initial state should be also `Presenting`.
- In `RedrawRequested`, assert it is `Presenting`, and set it to `NeedUpdate`, and then notify on the condvar."

**Problem**: While main thread held lock to blit, then dropped and reacquired it, renderer could grab lock and transition to `ComputingUpdate` before next `RedrawRequested`.

**Solution**: Added `Presenting` as barrier state:
- `Presenting` - Main thread blitting/presenting, renderer must wait
- `NeedUpdate` - Ready for renderer to start
- `ComputingUpdate` - Renderer computing
- `Updated(texture)` - Ready to blit
- `Exit` - Shutdown signal

**Key insight**: `Presenting` prevents renderer from transitioning `NeedUpdate` while main thread is between blit and request_redraw().

### Episode 3: Parallelism Optimization (Compute Before Wait)

User wanted more parallelism between presentation and computation.

**User**: "introduce a bit more parallelism between the main thread presents, and the renderer computes a step... move the wait on `SceneState::NeedUpdate` to after when a step has been computed... rename `ComputingUpdate` to `Rendering`"

**Problem**: Renderer waited for `NeedUpdate` at loop top before computing, couldn't overlap with main thread's presentation.

**Solution**: Restructure renderer loop:
1. Compute next frame (parallel with main presenting previous frame)
2. Wait for `NeedUpdate` state
3. Render computed state to texture

**Key insight**: By computing before waiting, renderer overlaps computation with presentation phase. Wait only happens before rendering (which requires previous frame consumed).

**State rename**: `ComputingUpdate` → `Rendering` (computation now happens before state transition).

## GIF Recording Feature

**User**: "Add a command line option to save the run to a gif file, and implement it using https://docs.rs/gif/latest/gif/"

### Security Audit

User required security audit before adding dependencies. Vendored gif crate v0.13.3 and reviewed:
- Uses `#![forbid(unsafe_code)]`
- Maintained by image-rs team
- Proper error handling
- **Verdict: SAFE TO USE**

### Three-Thread Architecture Evolution

**Initial**: Frame capture in renderer with blocking buffer mapping.

**Problem**: Buffer mapping blocked renderer thread on GPU operations.

**User's guidance**: Move blocking operations to dedicated encoder thread with state-based frame skipping.

**Final architecture**:
1. **Main thread**: Event loop, texture blitting, presentation
2. **Renderer thread**: Computation, scene building, rendering, frame capture coordination
3. **GIF encoder thread**: Buffer mapping (blocking), RGBA→grayscale conversion, GIF encoding

### GifEncodeState Machine

**User**: "It's ok for the gif to miss frames, expected event, so add a `Encoding` variant to `GifEncodeState`, and only send a new frame if it is `Idle`."

Coordinating renderer and encoder:
- `Idle` - Encoder ready to receive frame
- `HasBuffer(Arc<wgpu::Buffer>)` - Buffer ready to process
- `Encoding` - Processing frame
- `Exit` - Terminal state

Renderer checks encoder state before capturing: only if `Idle`, skip if `Encoding`.

**User**: "`GifEncodeState::Encoding` at the top of the encoder is unreachable(or should be)."

Made invariant explicit: `Encoding` is `unreachable!()` in encoder's wait loop.

**User**: "In the definition of an enum expressing a state machine like `GifEncodeState`, it's good practice for the variant to be, if possible, defined in the order in which they will occur in practice."

Reordered variants: Idle → HasBuffer → Encoding → Idle, Exit.

### Non-Blocking Frame Capture Flow

1. Renderer checks if encoder is `Idle` (skip if busy)
2. Renderer creates buffer, submits GPU copy (non-blocking)
3. Renderer sends `Arc<wgpu::Buffer>` to encoder
4. Encoder maps buffer (blocking, isolated to encoder thread)
5. Encoder converts RGBA→grayscale, writes GIF frame (6/100s delay)
6. Encoder transitions back to `Idle`

### wgpu 26.0.1 API

Initial implementation used incorrect type names from older wgpu. User provided Servo's vello_backend.rs as reference:
- `wgpu::TexelCopyBufferInfo` (not `ImageCopyBuffer`)
- `wgpu::TexelCopyBufferLayout` (not `ImageDataLayout`)
- `wgpu::PollType::Poll`/`::Wait` (not `Maintain` enum)

### Iterative Refinement (Episodes 4-7)

The GIF recording feature required significant iteration to achieve the desired performance and correctness. The following episodes show how the state machine evolved to handle GIF capture without blocking the main thread or compromising frame rates.

### Episode 4: GIF Performance Bottleneck

**Performance investigation**: User profiling showed main thread spending significant time in `queue.submit`. I initially explained as VSync, but user corrected with data:
- **With GIF**: `queue.submit` taking 24% of main thread time
- **Without GIF**: `queue.submit` taking only 0.18% of time

**User identified root cause**: GPU contention. Main thread (display blit) and renderer thread (GIF texture copy) submitting GPU work simultaneously, causing main thread to block.

**User's solution**: "Ok we can try to deal with the gif bottleneck by actually doing that when presenting is finished"

Make GIF capture conditional on thread scheduling - only capture if renderer scheduled before main handles next redraw.

### Restructuring for Opportunistic GIF Capture

**Changes**:
1. Add `Presented` state to signal presentation complete
2. Remove `Rendering` state (no longer needed)
3. Renderer waits for `Presented` OR `NeedUpdate` (whichever comes first)
4. Only capture GIF if `Presented` seen (renderer scheduled before main's next redraw)
5. Skip GIF if `NeedUpdate` arrives first (main scheduled first)

**Key design**: GIF capture depends on thread scheduling, not deterministic timing. When it happens, runs in parallel with renderer computing and scene building. Hope: GIF GPU work completes before renderer needs GPU for rendering. GIF never interferes with main thread's GPU usage.

**Final state machine** (5 states):
- `Presented` - Frame presented, ready for next
- `NeedUpdate` - Main requests new frame
- `Updated(texture)` - Renderer has frame ready
- `Presenting` - Main blitting/presenting
- `Exit` - Shutdown signal

**Flow without GIF**:
```
Renderer: Compute → Render → Wait(NeedUpdate) → Updated → [loop]
Main: Presented → NeedUpdate → Updated → Presenting → Presented
```

**Flow with GIF**:
```
Renderer: Compute → Render → Wait(NeedUpdate) → Updated → RenderComplete →
          Wait(Presented|NeedUpdate) → [if Presented] Capture GIF (parallel with next compute) → [loop]
Main: Presented → NeedUpdate → Updated → Presenting → Presented
```

### Episode 5: Race Condition Fix (Deadlock)

**Problem**: Application worked without GIF but hung with GIF recording. Added debug prints to trace.

**Issue**: After renderer sends `RenderComplete`, it waits for `Presented`. But main thread cycles through `Updated → Presenting → Presented → NeedUpdate` quickly. By the time renderer checks state, it's already `NeedUpdate` for next frame. Renderer stuck waiting for `Presented` on condvar, but notification came and went before it started waiting. Deadlock.

**User diagnosed**: "the renderer does not get notified until after the redraw requests comes in, and so it is stuck on the wait on the condvar"

**User's solution**: Break out on both `Presented` AND `NeedUpdate`, but only capture if got `Presented`:

```rust
let got_presented = match wait_for(Presented | NeedUpdate) {
    Presented => true,
    NeedUpdate => false,  // Next frame started, skip capture
};
let should_capture = got_presented && encoder_is_idle();
```

**Key insights**:
1. Renderer must not block waiting for state that may have passed
2. Accept both states, track which arrived first with boolean
3. Only capture GIF if `Presented` came first (thread scheduling allows it)
4. If `NeedUpdate` first (main scheduled before renderer), skip GIF frame
5. Combine "got_presented" with encoder idle check for final decision
6. When GIF captures, runs parallel with renderer computing next frame
7. Hope GIF GPU work completes before renderer's render phase needs GPU

**Performance characteristics**:
- GIF capture is opportunistic, depends on OS thread scheduling
- Which thread scheduled first (renderer vs main) determines capture
- When captured: runs parallel with renderer's compute/scene building
- GIF GPU work ideally completes before renderer's render phase
- Main thread never blocks on GIF work
- Graceful frame skipping based on scheduling

**State machine updates**:
- `RedrawRequested` expects `Presented` (not `Presenting`)
- `RenderComplete` transitions `Updated → Presenting → Presented`
- Renderer only waits for `Presented` when GIF recording enabled
- Initial state is `Presented` (ready for first frame)

### Episode 6: Thread Cleanup and Shutdown

**User**: "keep the join handle to the encoder, join on it when you exit"

**User**: "Add a `Exit` variant to the surface. When `WindowEvent::CloseRequested`, set the surface state to it, and when the renderer encounters that state, it breaks out of it's main loop(exits). In `ApplicationHandler::exiting`, you can then also join on the thread."

**Hierarchical shutdown**:
1. Renderer detects `SceneState::Exit`
2. Renderer signals encoder with `GifEncodeState::Exit`
3. Renderer joins encoder thread handle
4. Clean termination

### Episode 7: Texture Pooling Optimization

**User**: "In the renderer, instead of creating a new texture each time, I think we can use two textures, initially each None, and then create and render to the one that isn't being presented. So renderer owns two `Option<Arc<Texture>>`, called `presenting` and `rendering`, and mem swaps them when the main thread asks for an update. `SceneState::Updated` can then just clone the Arc (not the texture)."

**Problem**: Creating a new `wgpu::Texture` on every frame was wasteful—allocating GPU memory and duplicating texture data unnecessarily.

**Solution**: Texture pooling with double buffering:
- Renderer owns two `Option<Arc<wgpu::Texture>>`: `presenting` (currently shown) and `rendering` (next frame)
- Both start as `None` and are lazily created on first use with `get_or_insert_with()`
- After rendering, the renderer swaps them: `std::mem::swap(&mut presenting, &mut rendering)`
- `SceneState::Updated` sends `Arc::clone(presenting.as_ref().unwrap())` — cloning the Arc pointer, not the texture data
- GIF capture uses `presenting.as_ref().unwrap()` to access the just-presented texture (guaranteed `Some` after first frame)

**Code clarity**: Also simplified the GIF capture conditional by removing the intermediate `should_capture` variable and checking `if got_presented && encoder_is_idle` directly.

**Result**: Only two textures created total (instead of one per frame), efficient GPU memory reuse, thread-safe via Arc. Main thread and renderer never access the same texture simultaneously. Tested working in both GIF and non-GIF modes.

### Episode 8: Simplified Initial Condition & Deterministic GIF Capture

**User**: "try a single black cell top left for the part of the board that is visible (the rest stays the same)"

Changed initialization from random first row to deterministic single-cell start:
- Single `CellState::One` at top-right of visible area (`VISIBLE_BOARD_WIDTH - 1`)
- Rest of first row initialized to `CellState::Zero`
- Removed `rand` dependency (no longer needed)

This provides a cleaner, more reproducible way to observe Rule 110's evolution from minimal initial conditions—demonstrating how complexity emerges from simplicity.

**User**: "change the '// Capture frame to GIF if recording' logic so that instead of doing the `got_presented` stuff, it simply records reliably once every x frames, default 10. Add a command line argument"

Simplified GIF capture from complex thread-scheduling-based opportunistic capture to simple frame-counting approach:

**Problem with previous approach**: GIF capture depended on which thread (renderer vs main) got scheduled first—unpredictable and dependent on OS scheduling. The "wait for Presented OR NeedUpdate" logic was complex and made GIF recording timing non-deterministic.

**New approach**:
- Added `--gif-frame-skip <N>` command-line argument (default: 10)
- Renderer maintains `frame_counter` that increments every frame
- Captures GIF when `frame_counter % gif_frame_skip == 0` AND encoder is idle
- Removed complex "wait for Presented" logic entirely
- Still checks encoder idle state to avoid overwhelming it

**Benefits**:
- **Deterministic**: Always captures every Nth frame (e.g., frames 10, 20, 30...)
- **Predictable**: GIF timing independent of thread scheduling
- **Configurable**: Users control trade-off between smoothness and file size
- **Simpler**: Removed state machine complexity around `Presented` state coordination
- **Reliable**: No missed frames due to scheduling races

**Changes**:
- Added `gif_frame_skip: usize` field to `SharedState`
- Added `--gif-frame-skip` argument to CLI (default: 10)
- Added `frame_counter: usize` to renderer loop
- Simplified capture logic: `if frame_counter % gif_frame_skip == 0 && encoder_is_idle`
- Removed all `got_presented` wait logic

**Usage examples**:
```bash
# Record every 10th frame (default, balanced)
./automata --record-gif output.gif

# Record every frame (smooth but large/slow)
./automata --record-gif output.gif --gif-frame-skip 1

# Record every 30th frame (small/fast but choppier)
./automata --record-gif output.gif --gif-frame-skip 30
```

This change trades opportunistic parallelism (sometimes capturing in parallel with compute) for deterministic, predictable GIF recording that users can easily reason about and control.

### Episode 9: Inverted Pause Behavior

**User**: "Now another change: system pauses while space is pressed."

Changed the pause/unpause behavior to be inverted from the original design:

**Previous behavior**:
- Started paused
- Press and hold SPACE to run
- Release SPACE to pause

**New behavior**:
- Starts running immediately
- System runs automatically when SPACE is not pressed
- Press and hold SPACE to pause
- Release SPACE to resume

**Changes**:
- Changed initial `paused` state to `false` (start running)
- Inverted logic: `self.paused = should_pause` instead of `self.paused = !should_work`
- Changed trigger condition: unpause when space released (`was_paused && !should_pause`)
- Kept automatic `request_redraw()` on startup (starts running immediately)
- Updated comments to reflect new behavior

**Rationale**: This behavior is more intuitive—the system runs by default and you press SPACE to pause and examine the current state, rather than having to hold down a key continuously to watch the evolution.

### Episode 10: Reset Functionality

**User**: "Now also reset the system when escape is pressed"

Added ability to reset the automaton back to its initial state (single black cell) by pressing ESCAPE.

**Implementation challenges**: Initial attempt added a separate `SceneState::Reset` variant, but this caused complex state machine coordination issues and multiple panics due to texture lifecycle management. User reverted those changes.

**User's clean solution**: "Here is how to do reset cleanly: `NeedUpdate(bool)`, when true, simply reset the board and start from the initial state again"

**User's additional guidance**:
- "so handle the flag at the subsequent iteration to keep things simple" - Reset happens in renderer's next iteration, not immediately
- "No, need update should be also a local flag on the main thread, and you set it on the scene at the next redraw request" - Store flag locally on main thread, pass to state machine only during `RedrawRequested`
- "no need to request a redraw as part of escape, just rely on the ongoing redraw loop" - Don't explicitly trigger redraw; flag will be picked up naturally

**Implementation**:
- `NeedUpdate(bool)` where `true` means reset before rendering
- Main thread stores local `need_reset: bool` flag in `App` struct
- ESCAPE key handler simply sets `need_reset = true` (no state machine interaction, no explicit redraw)
- On next `RedrawRequested`, pass flag to `NeedUpdate(reset)` and immediately clear it to `false`
- Renderer checks flag at beginning of next iteration; if true, recreates board, resets `current_step` and `frame_counter`
- Reset happens before computation/rendering, at natural point in renderer loop

**Key insights**:
1. Simple parameter addition cleaner than new state variant
2. Local flag on main thread avoids race conditions
3. Flag communicated once per frame through existing state machine
4. Reset happens at natural point in renderer loop (beginning of iteration)
5. No immediate redraw needed - flag picked up by ongoing loop

**Benefits**:
- Race-free: reset state lives on main thread
- Simple: one boolean parameter, one local flag
- Clean: reuses existing state machine structure
- Reliable: reset applied at safe point in renderer lifecycle

**Changes**:
- Added `need_reset: bool` field to `App` struct (initialized to `false`)
- Changed `SceneState::NeedUpdate` to `NeedUpdate(bool)`
- ESCAPE handler sets `self.need_reset = true`
- `RedrawRequested` passes `need_reset` flag and clears it
- Renderer checks flag and resets board/counters if `true`

## Code Quality

**User**: "remove prints(except the two re missed frame). `GifEncodeState::Encoding` at the top of the encoder is unreachable(or should be)."

Removed unnecessary prints (kept diagnostic warnings). Made state machine invariant explicit: `Encoding` is `unreachable!()` in encoder's wait loop.

## Current Architecture

**Three threads**:
- **Main**: Event loop, texture blitting, presentation
- **Renderer**: Computation (parallel with presentation), scene building, rendering, GIF capture coordination
- **Encoder**: Buffer mapping (blocking), RGBA→grayscale, GIF encoding

**Render-to-texture**: Renderer renders to wgpu texture, main blits to surface with `TextureBlitter`.

**Shared resources**: Single device/queue Arc-shared between threads.

**Data structures**:
- Circular buffer with `row_offset` for O(1) scrolling
- Board: 4000×300 cells, viewport: leftmost 400×300
- Cyclic boundaries (wraps at edges per TLA+ spec)

**State machines**:
- `SceneState` (5 states): Presented, NeedUpdate(bool), Updated, Presenting, Exit
  - `NeedUpdate(bool)`: bool parameter indicates if reset is needed before rendering
- `GifEncodeState` (4 states): Idle, HasBuffer, Encoding, Exit

**Reset mechanism**:
- Main thread maintains local `need_reset` flag
- ESCAPE key sets `need_reset = true` (no immediate redraw request)
- On next `RedrawRequested`, passes flag to `NeedUpdate(reset)` and clears it
- Renderer checks flag; if true, recreates board and resets counters before rendering
- Simple and race-free: reset state lives on main thread, communicated once per frame

**Parallelism**: Renderer computes frame N+1 while main presents frame N.

**GIF capture**: Deterministic frame-counting approach - captures every Nth frame (configurable via `--gif-frame-skip`, default 10). Still checks encoder idle state to avoid overwhelming it. Simpler and more predictable than previous thread-scheduling-based approach.

**Initial condition**: Single black cell at top-right of visible area (`VISIBLE_BOARD_WIDTH - 1`), rest of first row zeros. Demonstrates complexity emerging from minimal starting state.

**Non-blocking**: Renderer never blocks on GPU operations.

**Frame skipping**: Graceful handling when encoder busy.

**Infinite scrolling**: Shifts by 10 rows when board fills.

**Clean shutdown**: Exit states propagate, threads join properly.

**Texture pooling**: Two `Option<Arc<wgpu::Texture>>` owned by renderer, swapped with `std::mem::swap()` after rendering. Only two textures created total, avoiding per-frame allocation overhead.

**Dependencies**:
- winit 0.30 - Window management
- vello 0.6.0 - 2D rendering
- wgpu 26.0.1 - GPU API
- pollster 0.3 - Block on async operations
- clap 4.5 - CLI parsing (with derive feature)
- gif 0.13 - GIF encoding

## Event Flow

```
SPACE released → request redraw (if was paused)
ESCAPE pressed → set need_reset flag
RedrawRequested (state: Presented) → set NeedUpdate(need_reset) + clear flag + notify renderer
Renderer (computed and waiting) receives NeedUpdate(reset) → [if reset] recreate board & reset counters → renders to texture → Updated(texture) + RenderComplete
RenderComplete → take texture + set Presenting + blit to surface + present → set Presented + notify
[If GIF enabled] Increment frame_counter; if frame_counter % gif_frame_skip == 0 and encoder idle → capture GIF
Loop continues via next RedrawRequested

Parallelism: Renderer computes frame N+1 while main thread presents frame N
GIF capture: Deterministic - every Nth frame where N is configurable (default 10)
GPU coordination: GIF capture happens after rendering, runs in parallel with next frame's computation
Reset: Local flag on main thread, passed once per frame, applied in renderer before computation
```
