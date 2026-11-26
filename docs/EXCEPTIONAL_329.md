# P(329,329) = 36,391

Here `k=109`, so the unrestricted bound `U(k)` is 36,392. Equality
would require one charge of 72, 374 runs, and either two perimeter
gaps with no isolate or one gap with one isolate. Both are excluded.

**Two gaps.** Use the [frame exchange and ordinary-bridge theorem](EXCEPTIONAL_287.md#all-size-reduction-the-two-gap-perimeter-can-be-prescribed)
to test only `0011`. In the crop obtained by deleting the two outer
rings, assign the marked NW and NE gap-corner teeth `(2,2)` and
`(2,326)` distinct labels 1 and 2, and assign all other marked teeth
label 0. On each crop edge forced by either endpoint require its two
labels to agree. This permits a bridge between any two ordinary teeth;
it forbids a bridge with either gap tooth as endpoint. It is necessary:
each non-bridge crop component has exactly one tooth. Also prohibit the
charged exit at the surviving feet `(2,0)` and `(0,326)`. The full-board
test retains the usual matching, rooted orientation, single boundary
exit and deep-axis clauses. Its 1,724,167 variables and 20,419,034
clauses yielded a checked contradiction.

**One gap.** Apply the one-gap canonical frame `0133` after putting
the isolate on the north arm. The 107 distances `5,8,...,323` are the
entire candidate list. Both axis branches use the 169 base and 198
additional certified tile templates, with their mark labels and
stencil types checked at 329. A single area-mod-2 test of 167–323
timed out; the two separate verified intervals below cover it.

| case | coverage | CNF SHA-256 | DRAT resolution steps |
|---|---|---|---:|
| two gaps | canonical `0011`, ordinary bridge | `737e630719ba69df981a07283d24397617f4e07359a33cf61c78d7d60d6cce44` | 2460915 |
| one gap, axis 2 | all 107 distances | `903139bf87872dd82dc9b2b0a1a0f11c7f6c5b85af56492967e881e96d9bd20a` | 26170 |
| one gap, axis 1 | 5–164, step 3 | `49a7474e1780ef393a714ba327aca19d2f50ec0f561b70c541f8945f1942d07b` | 117729 |
| one gap, axis 1, area mod 2 | 167–242, step 3 | `df5789ed268f01d10c7d708703050e4c8aa0bb715856afd28aec8cdfa553dcc9` | 82906 |
| one gap, axis 1, area mod 2 | 245–323, step 3 | `44c5474276620135d216bf56f2cb6ef8647f3bc32c3da5d525615dc2cda69330` | 7690853 |

The ledger replayed all five proofs with `drat-trim` and checked that
the distance ranges cover each axis. The physical rail replay was
`(36391,108239,2,108240,36391)`: adding one edge joins the two forced
components and gives a spanning tree with 36,391 full-degree vertices.
This proves the unrestricted result at 329; it does not transfer the
whole-board exclusions to 371.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.two_gap_board 329 240 0011 --axis --stream --ordinary-bridge
python3 -B -m analysis.research_program.tile_family_board 329 2 --sat --colors=2 --all-phases --dist=5:323
python3 -B -m analysis.research_program.tile_family_board 329 1 --sat --colors=2 --all-phases --dist=5:164
python3 -B -m analysis.research_program.tile_family_board 329 1 --sat --colors=2 --all-phases --dist=167:242 --area=2
python3 -B -m analysis.research_program.tile_family_board 329 1 --sat --colors=2 --all-phases --dist=245:323 --area=2
python3 -B -m analysis.research_program.exceptional_287_ledger --329 --drat
```
