## Rule 110 Cellular Automaton Visualizer

Displays the evolution of a 1D [Rule 110](https://mathworld.wolfram.com/Rule110.html) cellular automaton as a 2D history.

- Press and hold SPACE to compute and render (10 rows per frame)
- Release SPACE to pause
- Board starts with random row and scrolls infinitely
- Uses cyclic boundaries (wrapping at edges)

TLA+ [spec](spec.tla) written by hand; code generated as a result of a conversation [summarized here](conv.md) for technical highlights and evolution of the implementation.