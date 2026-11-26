# P(497,497) = 82,807

For `k=165`, the unrestricted bound is `U(k)=82,808`. Equality would
require one or two perimeter gaps. The [two-gap bound](CORE_413_UNIFORM.md)
requires the exit distances from the two north corners to be at least
308 each, whereas they sum to 496.

For one gap, use the canonical `0133` perimeter with the isolate on
the north arm. Both deep axes were tested over the entire distance
list `5,8,...,491`. Each range below uses step three:

| Axis | Isolate distances | Count | Verified resolution steps |
|---|---|---:|---:|
| 2 | 5–491 | 163 | 64,413 |
| 1 | 5–248 | 82 | 578,263 |
| 1, area modulo 2 | 251–371 | 41 | 9,397,025 |
| 1, area modulo 2 | 374–431 | 20 | 24,732,812 |
| 1, area modulo 2 | 434–491 | 20 | 37,044,484 |

The ledger checks the CNF hashes, the physical tile stencils and the
distance partition for each axis, then replays all five DRAT proofs.
Physical rail replay returned `(82807,247007,2,247008,82807)`:
one added edge joins the two components into a spanning tree on all
247,009 sites with exactly 82,807 full-degree vertices. Thus the lower
and upper bounds agree. The next unresolved exceptional side is 539.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.tile_family_board 497 2 --sat --colors=2 --all-phases --dist=5:491 --seconds=360
python3 -B -m analysis.research_program.tile_family_board 497 1 --sat --colors=2 --all-phases --dist=5:248 --seconds=360
python3 -B -m analysis.research_program.tile_family_board 497 1 --sat --colors=2 --all-phases --dist=251:371 --area=2 --seconds=600
python3 -B -m analysis.research_program.tile_family_board 497 1 --sat --colors=2 --all-phases --dist=374:431 --area=2 --seconds=840
python3 -B -m analysis.research_program.tile_family_board 497 1 --sat --colors=2 --all-phases --dist=434:491 --area=2 --seconds=840
python3 -B -m analysis.research_program.exceptional_287_ledger --497 --drat
```
