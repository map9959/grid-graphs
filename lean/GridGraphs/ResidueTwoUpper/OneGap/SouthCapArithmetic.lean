import Mathlib

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap

def width (h : Nat) := 3*h/4+3
def firstRow (k h : Nat) := 1+3*(k-h)
def firstCol (k h : Nat) := 1+3*(k-width h)

/-- The crop reaches the last interior row and column. The following
sites are the actual south and east rims. -/
theorem crop_bounds {u h : Nat} (k : Nat) (eq : k=11+14*u)
    (hk : 59≤k) (lo : 14≤h) (hi : h≤43) :
    4≤firstRow k h ∧ 4≤firstCol k h ∧
      firstRow k h+3*h+1=35+42*u ∧ firstCol k h+3*width h+1=35+42*u := by
  unfold firstRow firstCol width
  omega

/-- The axis test reaches strictly beyond the region of `DeepAfter`,
even at the smallest requested cap height. -/
theorem uncovered_tile {k h : Nat} (hk : 59≤k) (lo : 14≤h) (hi : h≤43) :
    let j := k-5
    k-h < j ∧ k-width h≤j ∧ j < k ∧ 4≤j ∧ j+5≤k ∧ ¬j+7≤k := by
  unfold width; dsimp only; omega

/-- Right-aligned tags for plaquette origins: the last origin is
two tile indices from the exclusive end, hence tag 12, not 13. -/
def endTag (extent index : Nat) := if index+8≤extent then 6 else 14+index-extent

theorem tag_range {extent index : Nat} (fit : index+2≤extent) :
    6≤endTag extent index ∧ endTag extent index≤12 := by
  unfold endTag
  split <;> omega

/-- The 119-board representative was selected by taking the last
origin in each bucket; the ordinary middle tag is at tile 31 and
the last six tags have consecutive representatives at tiles 32–37. -/
def repTile (t : Nat) := if t=6 then 31 else t+25

/-- The halo is `[origin-6,origin+12)`, clipped only at the true end.
In a middle bucket it is unclipped, and for the other six buckets
its distance to the true rim agrees exactly with the representative. -/
theorem halo_tag {k extent i : Nat} (hk : 59≤k) (he : extent≤43) (hi : i+2≤extent) :
    let orig := 1+3*(k-extent+i)
    let t := endTag extent i
    let rep := 1+3*repTile t
    6≤orig ∧ 6≤rep ∧ orig%3=rep%3 ∧
      (t=6 ∧ orig+12≤3*k+2 ∧ rep+12≤119 ∨
       7≤t ∧ (3*k+2)-orig=119-rep) := by
  dsimp only
  unfold endTag repTile
  split_ifs <;> omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
