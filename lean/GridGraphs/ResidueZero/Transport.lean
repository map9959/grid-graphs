import Mathlib.Tactic

/-! All-width local type transport for the residue-zero physical stencil. -/
namespace GridGraphs.ResidueZero

/-- Out-of-bounds queries have their own sentinel, even in a reflected view. -/
def axis (size depth i : Int) : Int :=
  if i < 0 ∨ size ≤ i then -1
  else if i < depth then i
  else if i < size-depth then depth+(i-depth)%3
  else 2*depth+3+i-size

def rep (base j i : Int) : Int :=
  if i < 6 then i else if base+3*j-6 ≤ i then i-3*j else 6+(i-6)%3

theorem rep_bounds {base j i : Int} (hb : 19 ≤ base) (hj : 0 ≤ j)
    (hi : 0 ≤ i) (his : i < base+3*j) :
    0 ≤ rep base j i ∧ rep base j i < base := by
  unfold rep
  split_ifs <;> omega

def view (flip : Bool) (s i : Int) := if flip then s-1-i else i

/-- Every shifted depth-two query agrees with its base-board representative.
The four units of collar beyond the coarse depth absorb both the offset
and the possible size change from passing between stars and patches. -/
theorem transport_coarse {b j i δ t : Int} (hb : 19 ≤ b) (hj : 0 ≤ j)
    (hδ : -2 ≤ δ ∧ δ ≤ 2) (ht : -2 ≤ t ∧ t ≤ 2) (flip : Bool) :
    axis (b+3*j+δ) 2 (view flip (b+3*j) i+t) =
    axis (b+δ) 2 (view flip b (rep b j i)+t) := by
  cases flip <;> simp [view,rep,axis] <;> split_ifs <;> omega

/-- Normalization labels, in both orientations, for stars (depth 6)
and patches (depth 5). Two axes can be independently reflected and swapped. -/
theorem transport_fine {b j i d : Int} (hb : 19 ≤ b) (hj : 0 ≤ j)
    (hd : 0 ≤ d ∧ d ≤ 6) (flip : Bool) :
    axis (b+3*j) d (view flip (b+3*j) i) =
    axis b d (view flip b (rep b j i)) := by
  cases flip <;> simp [view,rep,axis] <;> split_ifs <;> omega

end GridGraphs.ResidueZero
