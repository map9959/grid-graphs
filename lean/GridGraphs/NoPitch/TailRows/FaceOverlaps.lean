import GridGraphs.NoPitch.TailRows.IncidenceLift
import GridGraphs.NoPitch.TailRows.IncidenceReplay

/-! Physical overlap cancellations in the residue-one tail.

`Incidence.moved_eq` identifies the
coarse label of a nearby endpoint from the fine centre alone, including the
change of board size between a site and a patch origin. Consequently the
two parity-base replays check local prices, never incidence frequencies.
`Incidence.lifted` sums those prices on the original forest using the
edge reversal, shared patch strip, and site/patch-origin bijection. -/

namespace GridGraphs.NoPitch.TailRows
open PitchCut Budget TailCoverage GridGraphs.NoPitch.Dual Incidence Finset
attribute [local irreducible] chart58 chart61
def incidenceBook (k : Nat) := if k%2=1 then book58 else book61

/-- The three non-face incidence blocks cancel on the actual forest
vector. No no-pitch or additional bound on the forest is needed here. -/
theorem incidences_tail {k} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (i : Fin (tailChart k).rows.size) (h : (incidenceBook k).sel i) :
    lhs (tailChart k) (physicalVector (tailChart k) F (out F)) i=0 := by
  apply lifted hk _ _ _ F acy i h
  by_cases odd : k%2=1 <;> simp [tailChart,incidenceBook,odd,replay58,replay61]

def faceOverlap (tags : Array Nat) (i : Nat) := tags[i]! == 6 || tags[i]! == 12
private def cover (D : Chart) (s l n : Nat → Bool) (B : Book) :=
  let tags := supportMasks D
  decide (∀ i : Fin D.rows.size, D.rows[i].sense=0 → ¬s i → ¬l i → ¬n i →
    B.sel i ∨ faceOverlap tags i)
private theorem cover58 : cover chart58 flow58 letters58 (normal buckets58) book58 := by native_decide
private theorem cover61 : cover chart61 flow61 letters61 (normal buckets61) book61 := by native_decide

/-- Only rows supported on face/patch or face/line columns remain. -/
theorem upper_of_face_overlaps {k} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (faces : ∀ i : Fin (tailChart k).rows.size, faceOverlap (supportMasks (tailChart k)) i →
      lhs (tailChart k) (physicalVector (tailChart k) F (out F)) i=0) : F.card ≤ squareScore (N k) := by
  apply upper_of_zero_overlaps hk F acy rows cols
  intro i eq nf nl nn
  have c : cover (tailChart k) (selected k) (letterSelected k) (normal (normBuckets k)) (incidenceBook k) := by
    by_cases odd : k%2=1 <;> simp [tailChart,selected,letterSelected,normBuckets,incidenceBook,odd,cover58,cover61]
  rcases of_decide_eq_true c i eq nf nl nn with h|h
  · exact incidences_tail hk F acy i h
  · exact faces i h

def familyCounts (D : Chart) (B : Book) :=
  let tags := supportMasks D
  let indices := List.range D.rows.size
  let retained := indices.filter fun i => D.rows[i]!.sense==0 && B.sel i
  ([1,2,3].map fun tag => (retained.filter fun i => tags[i]! == tag).length,
    [6,12].map fun tag => (indices.filter fun i => tags[i]! == tag).length)
theorem face_overlap_counts :
    familyCounts chart58 book58=([371,1183,1064],[369,84]) ∧
    familyCounts chart61 book61=([394,1197,1036],[363,69]) := by native_decide
end GridGraphs.NoPitch.TailRows
