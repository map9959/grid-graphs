import GridGraphs.NoPitch.TailRows.Normalization

namespace GridGraphs.NoPitch.TailRows
open GridGraphs.NoPitch.Dual TailCoverage PitchCut Budget
attribute [local irreducible] chart58 chart61

/-- Presence of a star, patch, face, or line term in each retained row
(four bits, in that order). Zero coefficients carry no support. -/
def supportMasks (D : Chart) : Array Nat := Id.run do
  let mut masks := Array.replicate D.rows.size 0
  for col in D.cols do
    let bit := match col.key%8 with
      | 0 | 1 => 1 | 4 => 2 | 2 => 4 | 3 => 8 | _ => 16
    for (i,v) in col.terms do
      if v != 0 then masks := masks.setIfInBounds i (masks[i]?.getD 0 ||| bit)
  return masks

def pending (D : Chart) (flow letters norm : Nat → Bool) : List Nat :=
  (List.range D.rows.size).filter fun i => D.rows[i]!.sense==0 && !flow i && !letters i && !norm i

def remainingMaskCounts (D : Chart) (flow letters norm : Nat → Bool) :=
  let masks := supportMasks D
  let rows := pending D flow letters norm
  [1,3,2,6,12].map fun tag => (rows.filter fun i => masks[i]! == tag).length

/-- Counts by support, respectively star-only, star/patch, patch-only,
patch/face, and face/line. These five counts exhaust `remaining_counts`. -/
theorem overlap_census :
    remainingMaskCounts chart58 flow58 letters58 (normal buckets58)=[371,1064,1183,369,84] ∧
    remainingMaskCounts chart61 flow61 letters61 (normal buckets61)=[394,1036,1197,363,69] := by native_decide

def homogeneous (D : Chart) (B : Array NormShape) :=
  decide (∀ i : Fin D.rows.size, D.rows[i].sense=0 → ¬normal B i → D.rows[i].rhs=⟨0,0,0⟩)
private theorem hom58 : homogeneous chart58 buckets58 := by native_decide
private theorem hom61 : homogeneous chart61 buckets61 := by native_decide

/-- No width polynomial is left to establish. It suffices to show
literal cancellation of the remaining signed physical counts. -/
theorem upper_of_zero_overlaps {k : Nat} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (balance : ∀ i : Fin (tailChart k).rows.size, (tailChart k).rows[i].sense=0 →
      ¬selected k i → ¬letterSelected k i → ¬normal (normBuckets k) i →
      lhs (tailChart k) (physicalVector (tailChart k) F (out F)) i=0) : F.card ≤ squareScore (N k) := by
  have hom : homogeneous (tailChart k) (normBuckets k) := by
    by_cases odd : k%2=1 <;> simp [tailChart,normBuckets,odd,hom58,hom61]
  apply upper_of_overlap_rows hk F acy rows cols
  intro i s f l n
  rw [balance i s f l n,of_decide_eq_true hom i s n]; simp [Poly.atStep]

end GridGraphs.NoPitch.TailRows
