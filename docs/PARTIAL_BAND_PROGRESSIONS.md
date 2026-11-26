# Two sharp residue-two progressions with partial final bands

For every integer `t>=0`, let `T(k)=3k²+7k`. Then

| Side `n` | `k=(n−2)/3` | Exact `P(n,n)` |
|---|---|---|
| `23+42t` | `7+14t` | `T(k)−2t` |
| `41+42t` | `13+14t` | `T(k)−1−2t` |

In particular these include the progressions beginning at 65 and 83.
The upper half follows from the unrestricted period-three certificate.
Here the lower construction is `zipper_rails.build(n)` with no repair
and no delayed front. The proof uses a constant-size frontier calculation.

## Width-independent part

There are `F=(n−5)/6` advancing rows, `B` complete seven-row bands,
and a partial band of `r` rows, with parameters

| Side | `F` | `B` | `r` | Final left tip `M=3(F−B)` |
|---|---|---|---|---|
| `23+42t` | `3+7t` | `1+5t` | 5 | `6+6t` |
| `41+42t` | `6+7t` | `3+5t` | 6 | `9+6t` |

Indeed `n−8−F=7B+r`. The unmodified prefix proof in
[the zipper construction](RESIDUE_TWO_ZIPPER.md#geometry-and-why-it-stays-acyclic)
uses only `n=6F+5`: the approaching wedges meet the top bar, and the
exterior rails remain mutually disconnected. By the second regular row
the frontier consists of independent rail neighborhoods and an isolated
site in the four-column gap between the two tip rails.
Each complete band carries this partition to the second regular row of
the next band with the left tip decreased by three. This works also
for the last complete band: **both** partial endings have those first
two regular rows. Thus the input to the remaining calculation is
canonical at `A(M)`, the row marking `0,3,...,M` and `M+4,M+7,...,n−1`.

## The two endings have the same connectivity

After those two rows, mark `A(M)` plus the gap center `M+2` once.
Then repeat `A(M)` alone `r−3` times (two or three). In particular,
the sixth row of a *partial* six-row band is regular: it does not start
the tip shift of a complete band. The extra center joins the two tip
rails once. The gap site in the last regular row has no incident forced
edge to the preceding row or to a marked horizontal neighbor. Thus
both endings arrive at the cap with the gap site isolated and the two
tip rail neighborhoods identified, all others independent.

`partial_band_progressions.cap_test` checks precisely that partition,
as well as acyclicity at each step. It then attaches the three marked
cap rows, the empty row and the full bottom row. Each check contracts
only components already formed and rejects an edge whose endpoints
are already joined. Before adding the bottom row, every site of the
empty row belongs to a distinct component. Thus the new horizontal
bar and its distinct vertical attachments cannot create a cycle.

The representative has width 23 and `M=9`. For `t>=1` every required
terminal interface arises by inserting `(M−9)/3` pitches on the left
and `((n−M)−14)/3` pitches on the right. Both are nonnegative integers.
The same padding rule applies to the complete-band check of width 23
with starting tip 12: the last such band starts at `M+3`, and even the
first starts with at least 11 columns of width to its right (including
the right boundary in the width convention `n−L`). To pad a cap,
insert between fixed rails on either side of the changing central
pattern (e.g. between 0 and 3 on the left), never between the joined
tips. Each new three-column pitch supplies a separate straight rail
and its leaves until the empty row; there it supplies an independent
tip and two isolates. The full bottom bar attaches to the tip once.
It cannot change the central partition or introduce a cycle. For
`t=0` the two physical boards are checked directly, so no reduction
to a too-wide representative is needed.

## Count

The score, by summing the top, advancing rows, complete bands, partial
band and cap, respectively, is

```
(n−2 + 1 + k+1) + Fk + B[7(k+1)+1] + [r(k+1)+1] + (3k+3+n).
```

Substitution gives the tabled formulas. The certified upper correction
`floor((23−2k)/14)` is respectively `−2t` and `−1−2t`, giving equality.
As an algebra check the replay compares all three Newton coefficients
of the quadratic expressions, not three sampled tree scores.

```
python3 -B -m analysis.research_program.partial_band_progressions
```

This is a computer-assisted proof; no new Lean formalization is claimed.
