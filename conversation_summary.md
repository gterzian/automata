# Rule 110 Cellular Automaton Visualizer - Development History

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

### Race Condition During Startup
**User**: "Add another variant to the state enum: Presenting..."

Added `Presenting` state to fix race where renderer could consume `NeedUpdate` while main thread was between finishing blit and calling request_redraw.

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

### Thread Cleanup

**User**: "keep the join handle to the encoder, join on it when you exit"

**User**: "Add a `Exit` variant to the surface. When `WindowEvent::CloseRequested`, set the surface state to it, and when the renderer encounters that state, it breaks out of it's main loop(exits). In `ApplicationHandler::exiting`, you can then also join on the thread."

**Hierarchical shutdown**:
1. Renderer detects `SceneState::Exit`
2. Renderer signals encoder with `GifEncodeState::Exit`
3. Renderer joins encoder thread handle
4. Clean termination

### Code Quality

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
- `SceneState` (5 states): Presented, NeedUpdate, Updated, Presenting, Exit
- `GifEncodeState` (4 states): Idle, HasBuffer, Encoding, Exit

**Parallelism**: Renderer computes frame N+1 while main presents frame N.

**GIF capture**: Opportunistic based on thread scheduling; when it happens, runs parallel with renderer's compute phase. Which thread gets scheduled first (renderer/main) determines if GIF captured. GIF GPU work aims to complete before renderer's render phase needs GPU.

**Non-blocking**: Renderer never blocks on GPU operations.

**Frame skipping**: Graceful handling when encoder busy or when system falls behind.

**Infinite scrolling**: Shifts by 10 rows when board fills.

**Clean shutdown**: Exit states propagate, threads join properly.

**Dependencies**:
- vello 0.6.0 - 2D rendering
- wgpu 26.0.1 - GPU API
- winit - Window management
- gif 0.13.3 - GIF encoding
- clap 4.5 - CLI parsing

## Event Flow

```
SPACE pressed → request redraw
RedrawRequested (state: Presented) → set NeedUpdate + notify renderer
Renderer (computed and waiting) receives NeedUpdate → renders to texture → Updated(texture) + RenderComplete
RenderComplete → take texture + set Presenting + blit to surface + present → set Presented + notify
[If GIF enabled] Renderer waits for Presented|NeedUpdate (race based on thread scheduling)
  - If renderer scheduled first: sees Presented → captures GIF in parallel with next compute
  - If main scheduled first: sees NeedUpdate → skips GIF for this frame
Loop continues via next RedrawRequested

Parallelism: Renderer computes frame N+1 while main thread presents frame N
GIF capture: Opportunistic based on thread scheduling; when it happens, runs parallel to renderer compute
Thread scheduling: Random which thread (renderer/main) gets scheduled first determines GIF capture
GPU coordination: GIF GPU work aims to complete before renderer's render phase needs GPU
```

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
- **Parallel computation → Single-threaded**: Removed column-based parallelization with multiple renderer threads competing for shared board state. Simplified to single renderer thread with exclusive board ownership.
- **Dependencies pruned**: Removed rayon (no longer needed), later re-added clap for CLI args

### Key Bug Fixes

**gterzian**: "Don't always just listen to me, there is a bug in the setting of should compute to new paused"

Fixed condvar notification timing - was notifying unnecessarily when pausing.

**gterzian**: "At the beginning of the compute renderer loop, there is a bug based on the logic we added. Make sure you try to prevent these kind of side effects"

Fixed critical bug where renderer was immediately setting `should_compute = false` after waking up, breaking the processing loop.

**gterzian**: "Add another variant to the state enum: Presenting..."

Added `Presenting` state to fix race condition where renderer could consume `NeedUpdate` while main thread was between finishing blit and calling request_redraw.

### Infinite Scrolling
> **gterzian**: Instead of stopping at `Done`: keep "scrolling down" by popping a compute step from the top of the board, and pushing a compute step to the bottom.

User updated the TLA+ spec to support infinite evolution instead of stopping when the board fills. Implementation should be a refinement of the spec - maintaining all invariants while creating an infinite scrolling view.

Implemented circular buffer with `row_offset` for O(1) scrolling. When board fills, shifts by `STEPS_PER_FRAME` (10 rows) to match compute granularity. Initial attempt shifted by 1 row; user corrected to shift by the full compute step size for smoother scrolling.

## UI Evolution: Board Layout and Viewport

The visible board layout has evolved significantly to provide better visualization of the Rule 110 patterns.

### Initial Layout: Full Board Visible

Initially, the board was exactly the size of the window - what you compute is what you see. The entire automaton evolution was visible from left to right.

**Dimensions**:
- Board: 400×300 cells (matches window: 1600×1200 pixels at 4px per cell)
- Viewport: Shows entire board (400×300)

### Split-Screen Layout: 3x Wide Board, Middle Third Visible

To give the automaton more space to evolve complex patterns before displaying them, the board was made 3x wider than the window, with only the middle third visible.

**gterzian** (implicit from code evolution): Expanded board to provide "off-screen" evolution space.

**Dimensions**:
- Board: 1200×300 cells (3x wider than window)
- Viewport: Middle third (cells 400-799, showing 400 visible cells)
- Rationale: Patterns evolve in the left third, mature in the middle (visible), and dissipate in the right third

This "split-screen" approach provided context: patterns entering from the left had already evolved for some time, making the visible evolution more interesting.

### Wide Canvas Layout: 10x Wide Board, Leftmost Edge Visible

**gterzian**: "So now I want to make the board ten times as wide, and, retaining the same window size, only render the left most side of it."

Further expanded to give the automaton dramatically more horizontal space, viewing only the leftmost edge where evolution begins.

**Dimensions**:
- Board: 4000×300 cells (10x wider than window)
- Viewport: Leftmost portion (cells 0-399, showing 400 visible cells)
- Rationale: Massive horizontal space for complex pattern formation, with the window showing where evolution originates

This provides maximum space for the automaton to develop intricate patterns across a wide canvas, while focusing the viewport on the "birth" region where the evolution is actively spreading from the initial conditions.

### Evolution Rationale

The progression from 1x → 3x → 10x board width reflects an understanding that Rule 110 is computationally universal and can generate increasingly complex patterns given sufficient space. The viewport placement shifted from "middle third" to "leftmost edge" because:

1. **3x middle-third**: Showed mature, evolved patterns with context on both sides
2. **10x leftmost**: Shows the evolution's origin, where patterns are actively forming and propagating

The 10x layout is particularly suited for observing how local interactions at the evolutionary "wavefront" create emergent structure across the vast horizontal space.

## State Machine Evolution

### Episode 1: Initial Three-State Machine

**Initial problem**: Scene was being cloned on every frame. User suggested putting it in shared state.

**gterzian**: "do you need to clone the scene to send it to the main thread? Is that not something to add to the shared state instead?"

**gterzian**: "so put an `Option<Scene>` in `work_cv`, and use that to also replace the 'should work' boolean."

First attempt used `Option<Scene>` but had logic errors, leading to panics.

**gterzian**: "No so the problem is the renderer goes back to the beginning of the loop and then takes the scene again, so if the render event is received you can't be sure the scene is some. We need to do more than use an option around the scene, rather we need an enum with three variants: NeedUpdate(scene), ComputingUpdate, Updated(scene)."

Implemented proper three-state machine:
- `NeedUpdate(scene)` - Scene ready for renderer
- `ComputingUpdate` - Renderer computing
- `Updated(scene)` - Scene ready to render

**gterzian**: "only start the compute when RedrawRequested comes in, and only if not paused. This means RenderComplete should just keep the lock and use the scene, not set it immediately to NeedUpdate. Also, we want to re-use the same scene (make sure to reset it)."

Corrected flow: trigger compute from RedrawRequested instead of RenderComplete.

### Episode 2: Race Condition Discovery - Adding Presenting State

After Vello 0.6 migration with render-to-texture, discovered a subtle race condition that caused occasional panics.

**gterzian**: "You're right that on start-up, if the renderer sets the state to computing before redraw requested comes in, it will panic. But that doesn't happen often, I'm seeing a panic after a while only so far.

Ah I know what it is: in `RenderComplete`, main thread holds a lock, and only releases it at the end(actually it drops and re-aquires it). So the renderer thread could be at the top of its loop, not waiting on the condvar but waiting on the lock, and then reading `NeedUpdate` and setting is to computing, meaning that at the next redraw event it is not in `NeedUpdate` anymore.

This is how to address it:
- Add another variant to the state enum: Presenting, and in `RenderComplete`, take the state out, and replace it with `Presenting`, and drop the lock.
- Initial state should be also `Presenting`.
- In `RedrawRequested`, assert it is `Presenting`, and set it to `NeedUpdate`, and then notify on the condvar."

**The problem**: While main thread held lock to blit, then dropped and reacquired it to set NeedUpdate, the renderer could grab the lock in between and transition to ComputingUpdate before the next RedrawRequested.

**The solution**: Added `Presenting` state as a barrier:
- `Presenting` - Main thread is blitting/presenting, renderer must wait
- `NeedUpdate` - Ready for renderer to start computing
- `ComputingUpdate` - Renderer is computing
- `Updated(texture)` - Texture ready to blit
- `Exit` - Signal renderer to terminate

**Key insight**: `Presenting` prevents renderer from transitioning NeedUpdate while main thread is between finishing a blit and calling request_redraw().

### Episode 3: GIF Recording - Similar Pattern in GifEncodeState

When implementing GIF recording, encountered similar coordination issues.

**gterzian**: "It's ok for the gif to miss frames, expected event, so add a `Encoding` variant to `GifEncodeState`, and only send a new frame if it is `Idle`."

Applied same state machine pattern to coordinate renderer and encoder thread:
- `Idle` - Encoder ready to receive frame
- `HasBuffer(Arc<wgpu::Buffer>)` - Buffer ready to process
- `Encoding` - Processing frame
- `Exit` - Terminal state

Renderer checks encoder state before capturing: only capture if `Idle`, skip frame if `Encoding`.

**gterzian**: "`GifEncodeState::Encoding` at the top of the encoder is unreachable(or should be)."

Made invariant explicit: encoder sets `Encoding` itself and transitions out before looping back, so it should be `unreachable!()` in the wait loop.

### Episode 4: Parallelism Optimization - Compute Before Wait

After establishing the working three-thread system, user requested restructuring the renderer loop to enable more parallelism between computation and presentation.

**gterzian**: "introduce a bit more parallelism between the main thread presents, and the renderer computes a step... move the wait on `SceneState::NeedUpdate` to after when a step has been computed... rename `ComputingUpdate` to `Rendering`"

**The problem**: Renderer waited for `NeedUpdate` at the top of the loop before computing, meaning it couldn't compute during the main thread's presentation phase.

**The solution**: Restructure renderer loop to move computation before the wait point:
1. Check for `Exit` state (early termination)
2. Compute next frame (can run while main thread presents previous frame)
3. Wait for `NeedUpdate` state
4. Render computed state to texture

**Key insight**: By computing before waiting, the renderer can overlap computation with the main thread's presentation phase. The wait only happens before rendering (which requires the previous frame to be consumed). This maximizes parallelism while maintaining correctness.

**State rename**: `ComputingUpdate` → `Rendering` to better reflect that computation is done before the state transition.

### Episode 5: GIF Bottleneck and Critical Path Decoupling

**Performance Investigation**: User was profiling the application and noticed the main thread was spending significant time in `queue.submit`. I initially tried to explain this as VSync behavior, but user pointed out the profiling data showed a dramatic difference:
- **With GIF recording**: `queue.submit` taking 24% of main thread time
- **Without GIF recording**: `queue.submit` taking only 0.18% of time

User identified the root cause: GPU contention. Both the main thread (display blit) and renderer thread (GIF texture copy) were submitting GPU work simultaneously, causing the main thread to block waiting for the GPU.

**Solution proposed by user**: Make GIF capture conditional on thread scheduling - only capture if the renderer thread gets scheduled before the main thread handles the next redraw event.

**The solution**: Restructure the state machine and renderer loop to make GIF capture opportunistic based on thread scheduling:
1. Add `Presented` state to signal when presentation is complete
2. Remove unnecessary `Rendering` state
3. Make renderer wait for `Presented` OR `NeedUpdate` (whichever comes first based on thread scheduling)
4. Only capture GIF if `Presented` was seen (renderer scheduled before main thread's next redraw)
5. Skip GIF frame if `NeedUpdate` arrives first (main thread scheduled first for next redraw)

This makes GIF capture dependent on thread scheduling rather than deterministic timing. When GIF capture happens, it runs in parallel with the renderer thread computing and scene building. The hope is that by the time the renderer needs GPU access for rendering, the GIF capture GPU work is complete. Importantly, GIF work never interferes with the main thread's GPU usage.

### State Machine Restructure

**Changes**:
1. **Removed `Rendering` state** - No longer needed with new flow
2. **Added `Presented` state** - Signals presentation is complete
3. **Changed initial state** - From `Presenting` to `Presented`
4. **Made GIF wait conditional** - Only wait for `Presented` when GIF recording enabled

**New state machine** (5 states):
- `Presented` - Frame has been presented to screen, ready for next frame
- `NeedUpdate` - Main thread requests new frame computation  
- `Updated(texture)` - Renderer has computed and rendered new frame
- `Presenting` - Main thread is blitting and presenting
- `Exit` - Shutdown signal

**Flow without GIF**:
```
Renderer: Compute → Render → Wait(NeedUpdate) → Updated → [loop]
Main: Presented → NeedUpdate → Updated → Presenting → Presented
```

**Flow with GIF**:
```
Renderer: Compute → Render → Wait(NeedUpdate) → Updated → RenderComplete →
        Wait(Presented|NeedUpdate) → [if Presented & time available] Capture GIF (parallel with next compute) → [loop]
Main: Presented → NeedUpdate → Updated → Presenting → Presented
```

**Key insight**: GIF capture depends on thread scheduling - it only happens if the renderer thread is scheduled to check the state before the main thread processes the next redraw event. When GIF capture occurs, it runs in parallel with the renderer computing the next frame.

### Critical Race Condition Fix

**The problem**: After implementing the `Presented` state, the application worked without GIF but hung when GIF recording was enabled. I added debug prints to trace the state machine.

The issue: After renderer sends `RenderComplete`, it waits for `Presented`. But the main thread cycles through `Updated → Presenting → Presented → NeedUpdate` quickly. By the time the renderer checks the state, it has already moved to `NeedUpdate` for the next frame. The renderer is stuck waiting for `Presented` on the condvar, but the notification came and went before it started waiting, causing a deadlock.

**User diagnosed the issue**: "the renderer does not get notified until after the redraw requests comes in, and so it is stuck on the wait on the condvar"

**User's solution**: Break out of the wait on both `Presented` and `NeedUpdate`, but only capture the GIF frame if we actually saw `Presented`:

```rust
let got_presented = match wait_for(Presented | NeedUpdate) {
    Presented => true,
    NeedUpdate => false,  // Next frame started, skip this capture
};
let should_capture = got_presented && encoder_is_idle();
```

**Key insights from user**:
1. Renderer must not block waiting for a state that may have already passed
2. Accept both `Presented` and `NeedUpdate`, using a boolean flag to track which arrived first
3. Only capture GIF if `Presented` came first - determined by thread scheduling, not deterministic timing
4. If `NeedUpdate` arrives first (main thread scheduled before renderer), skip the GIF frame
5. Combine the "got_presented" flag with the encoder idle check for the final capture decision
6. When GIF capture happens, it runs in parallel with renderer computing the next frame
7. Hope that GIF GPU work completes before renderer needs GPU for rendering

**Performance impact**:
- GIF capture is opportunistic and depends on thread scheduling
- Which thread gets scheduled first (renderer vs main) determines if GIF is captured
- When GIF is captured: runs in parallel with renderer's compute/scene building phase
- GIF GPU work ideally completes before renderer's render phase needs GPU
- Main thread never blocks on or interferes with GIF work
- Renderer can compute frame N+1 during frame N presentation
- Graceful frame skipping based on scheduling

**State machine updates**:
- `RedrawRequested` handler expects `Presented` (not `Presenting`)
- `RenderComplete` transitions `Updated → Presenting → Presented`
- Renderer only waits for `Presented` when GIF recording enabled
- Initial state is `Presented` (ready for first frame)

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

User identified that buffer mapping was blocking the renderer thread on GPU operations, which was undesirable. Requested moving the blocking operations to a dedicated encoder thread, with state-based frame skipping when the encoder is busy. Multiple iterations to get the architecture right: first moved capture to renderer, then created dedicated encoder thread, then moved buffer mapping to encoder thread.

**Initial**: Frame capture in renderer with blocking buffer mapping.

**Problem**: GPU blocking in renderer thread during buffer mapping.

**Solution**: Three-thread system with dedicated encoder thread.

### Three-Thread Architecture
1. **Main thread**: Event loop, texture blitting, presentation
2. **Renderer thread**: Computation (parallel with presentation), scene building, rendering, frame capture coordination
3. **GIF encoder thread**: Buffer mapping (blocking operation), RGBA→grayscale conversion, GIF encoding

### GifEncodeState Machine
Variants ordered by occurrence:
- `Idle` - Encoder ready to receive frame
- `HasBuffer(Arc<wgpu::Buffer>)` - Buffer ready to process
- `Encoding` - Processing frame (unreachable in wait loop)
- `Exit` - Terminal state

### Non-Blocking Frame Capture Flow
1. Renderer checks if encoder is `Idle` (skip frame if busy)
2. Renderer creates buffer and submits GPU copy command (non-blocking)
3. Renderer sends `Arc<wgpu::Buffer>` to encoder thread
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

**gterzian**: "Add a `Exit` variant to the surface. When `WindowEvent::CloseRequested`, set the surface state to it, and when the renderer encounters that state, it breaks out of it's main loop(exits). In `ApplicationHandler::exiting`, you can then also join on the thread."

Implemented hierarchical shutdown:
1. Renderer detects `SceneState::Exit`
2. Renderer signals encoder with `GifEncodeState::Exit`
3. Renderer joins encoder thread handle
4. Clean termination

### Code Quality

**gterzian**: "In the definition of an enum expressing a state machine like `GifEncodeState`, it's good practice for the variant to be, if possible, defined in the order in which they will occur in practice."

Reordered enum variants to match actual state flow (Idle → HasBuffer → Encoding → Idle, Exit).

**gterzian**: "remove prints(except the two re missed frame). `GifEncodeState::Encoding` at the top of the encoder is unreachable(or should be)."

Removed unnecessary print statements (kept diagnostic warnings). Made state machine invariant explicit: `Encoding` is `unreachable!()` in encoder's wait loop, enforcing that encoder should never be in `Encoding` state at loop start.

## Architecture Summary

**Current system**:
- **Three threads**: Main (event loop + blitting), renderer (compute + render), encoder (GIF writing)
- **Render-to-texture**: Renderer renders to wgpu texture, main thread blits to surface
- **Shared device/queue**: Arc-wrapped, shared between threads
- **Circular buffer**: O(1) board scrolling using row_offset
- **State machines**: `SceneState` (5 variants: Presented, NeedUpdate, Updated, Presenting, Exit), `GifEncodeState` (4 variants)
- **Non-blocking**: Renderer never blocks on GPU operations
- **Frame skipping**: Graceful handling when encoder busy
- **Parallelism**: Renderer computes frame N+1 while main thread presents frame N
- **GIF capture**: Opportunistic based on thread scheduling; runs in parallel with renderer's compute phase
- **Board layout**: 10x wider than visible (4000×300), renders leftmost edge (400×300)
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
RedrawRequested (state: Presented) → set NeedUpdate + notify renderer
Renderer (computed and waiting) receives NeedUpdate → renders to texture → Updated(texture) + RenderComplete
RenderComplete → take texture + set Presenting + blit to surface + present → set Presented + notify
[If GIF enabled] Renderer waits for Presented|NeedUpdate (race based on thread scheduling)
  - If renderer scheduled first: sees Presented → captures GIF in parallel with next compute
  - If main scheduled first: sees NeedUpdate → skips GIF for this frame
Loop continues via next RedrawRequested

Parallelism: Renderer computes frame N+1 while main thread presents frame N
GIF capture: Opportunistic based on thread scheduling; when it happens, runs parallel to renderer compute
Thread scheduling: Random which thread (renderer/main) gets scheduled first determines GIF capture
GPU coordination: GIF GPU work aims to complete before renderer's render phase needs GPU
```
