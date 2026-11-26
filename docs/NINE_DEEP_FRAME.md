# A frame nine sites in from all four sides

For `n=3k+1≥103`, prescribe only the perimeter of the `(n-18)`-square
at offset `(9,9)`: both lateral sides completely marked, and both
end rows marked at columns `9,12,…,n-10`. Within this class the
exact optimum is the ordinary comb. All nine layers outside this
frame and all strictly interior sites are free.

Use the terminal accounting of [the three-column frame](JOINT_ALIGNED_FRAME.md),
now with `H=n-18` rows and `p=(n-16)/3` teeth per end. If `C` core
classes meet the teeth, `I≤Hp` and `I+C-p≤Hp` by the unwired seam
theorem. Cut the wings transversely. For each end maximize
`10*marks+7*classes`, separately for one terminal class and for at
least two. Sweep through each **bend diagonally** rather than keeping
the whole width of both incident arms simultaneously. Keep the
actual square sites, including the prescribed teeth and side bars,
subtracting their fixed marks from the answer. A touched component
gets the bonus only on disappearing. The three possible closed-class
counts `0,1,≥2` have separate prices on the same structural frontier.

* If both wings contain a pitch slice (`0,3,6` marked in the nine
  free sites) at least 18 rows from each end of the bar, split at
  those two slices. Their heights may be different. The two pieces
  share six extra marked groups: contract their forced seam edges,
  match the corresponding groups, and subtract the six duplicated
  marks. Set `q=p+6`. Otherwise ignore the transverse bonds and use
  `q=p`, with no duplicated marks. In both cases, for terminal-class
  counts `c_N,c_S`, `I-Hp≤min(0,c_N+c_S-q-1)` by the forest rank
  inequality. The four one/many cases are exactly those in the
  three-column proof.
* In the missing-pitch case reflect so the left wing has no eligible
  cut. Split with each half at least 42 rows long. In **each** piece
  forbid pitch on the 23 slices at distances 1 through 23 from the
  split endpoint. Every one of these lies in the qualifying interval.
  No profile on the other wing is needed.

For `103`, with 43 rows per piece in the first case the prices are
`6067,6064`. Keeping just the unconditioned price 6067 misses the
integer exclusion by one. With the four cases the upper is **3646**.
In the missing case the 42-row prices are `5957,5957`; the extra
wing rows add six marks, and the upper is **3641**.

**Arbitrary sizes.** In the first case the structural and all three
price vectors shift by 40 on an extra regular wing row at positions
15–16. In the absent case this happens at 37–38 after the forbidden
window; for the unrestricted wing use its unrestricted prefix in
the reflected sweep. In either case ten of the 40 units pay for a
fixed bar site, so each length increment adds 30 usable units. Once
the partial width vectors recur 30 columns apart the shift is 1100,
of which 100 belong to the fixed teeth. Regular columns have the
same ordered live neighbors, tags and masks after these insertions;
the two corners are translated intact. The prefix recurrence can
be used independently on either wing by reflection.

The pitch-family width checkpoints are 60 and 90, tested on the ten
widths from 103 to 130. In the absent case they are 90 and 120 on
widths 133 through 160, with the preceding ten widths checked
directly. On adding 30 to the square, the total usable price of the
two pieces rises by `2·1000+60·30=3800`, `q` rises by 10, and
`H,p` become `H+30,p+10`. After subtracting the terminal price,
the increase outside `Hp` is 373 marks in the many/many or mixed
cases and 370 in the one/one case. The comb increment less the
increment of `Hp` is exactly 373. This is a size induction, not
an assumption that the square's marking repeats.

```
rustc -O analysis/research_program/annular_frontier.rs -o target/annular_frontier
python3 -B -m analysis.research_program.wide_frame_caps --family
python3 -B -m analysis.research_program.wide_frame_caps --absent-family
```
