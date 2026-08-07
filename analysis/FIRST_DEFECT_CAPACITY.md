# First-defect capacity boundary

Let a row frontier have rooted attachment debt `d`, remaining graphic rank
`R`, and remaining U budget `B`. For the unprocessed square cap `S`, define

```text
C(S,B) = max over X subset S, |X|<=B of
         (U-U edges internal to X + U-U edges from X to processed U).
```

Every independent future merge that discharges current debt uses a distinct
future rank-increasing U-U edge. Therefore the suffix-free bound

```text
future current-debt merges <= min(d,R,C(S,B))
```

is valid. Row-major order gives `C(S,B)<=2B`. In a one-row terminal cap,
`C(S,B)` is exactly the two-state dynamic program implemented by
`maximum_terminal_row_edges` and `terminal_cell_edge_capacity`.

This bound cannot give a universal strict penalty after the first two-carrier
defect. The exact `n=8` defect witness reaches its first width-two frontier at
row 7 with

```text
d=4, R=4, B=3, C=5,
min(d,R,C)=4.
```

Its final row performs all four required merges and terminates connected. The
exact `n=11` defect witness reaches row 7 with `d=6` and its suffix likewise
discharges all six units. Thus assertions such as `capacity<=d-1`, `R-1`, or a
mandatory one-unit two-carrier loss are false.

The exact first-defect gap at `n=8,11` must instead be charged to the prefix and
defect-creation transition together with a lower bound on the remaining cap
weight. It is not a consequence of reduced future merge capacity.

Transposition does not create a simultaneous defect: both exact witnesses have
row-frontier width two but transposed width at most one. Side and bottom cap
penalties therefore cannot be intersected without a separate theorem forcing
both orientations.
