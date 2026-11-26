# P(455,455) = 69,439

Here `k=151`, so the unrestricted bound is `U(k)=69,440`. Equality
requires one or two perimeter gaps. The [two-gap transfer](CORE_413_UNIFORM.md)
requires both distances of the exit from the north corners to be at
least 308. They sum to 454, so that case is impossible.

For one gap, put the isolate on the north arm by transposition and
use the canonical `0133` perimeter. The 149 distances `5,8,...,449`
must be tested on both deep axes. The ledger checks the stencils and
catalogue hashes, verifies exact coverage per axis, then independently
replays each proof with `drat-trim`.

| Axis | Isolate distances (step 3) | Count | DRAT resolution steps |
|---|---|---:|---:|
| 2 | 5–449 | 149 | 54,056 |
| 1 | 5–227 | 75 | 415,064 |
| 1, area modulo 2 | 230–338 | 37 | 486,103 |
| 1, area modulo 2 | 341–392 | 18 | 91,784,688 |
| 1, area modulo 2 | 395–449 | 19 | 33,197,605 |

All five proofs returned `s VERIFIED`. Physical replay of the rail
returned `(69439,207023,2,207024,69439)`: adding one edge joined the
two forced components into a spanning tree on all 207,025 sites, with
exactly 69,439 full-degree vertices. This settles 455, not the entire
exceptional tail. At the next open side, 497, only one gap remains.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.tile_family_board 455 2 --sat --colors=2 --all-phases --dist=5:449 --seconds=300
python3 -B -m analysis.research_program.tile_family_board 455 1 --sat --colors=2 --all-phases --dist=5:227 --seconds=300
python3 -B -m analysis.research_program.tile_family_board 455 1 --sat --colors=2 --all-phases --dist=230:338 --area=2 --seconds=480
python3 -B -m analysis.research_program.tile_family_board 455 1 --sat --colors=2 --all-phases --dist=341:392 --area=2 --seconds=600
python3 -B -m analysis.research_program.tile_family_board 455 1 --sat --colors=2 --all-phases --dist=395:449 --area=2 --seconds=600
python3 -B -m analysis.research_program.exceptional_287_ledger --455 --drat
```
