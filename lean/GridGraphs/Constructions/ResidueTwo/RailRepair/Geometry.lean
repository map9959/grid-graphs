import GridGraphs.Constructions.ResidueTwo.ResidueTwoStaircaseForest

/-! # Actual terminal-rail repair coordinates

All graphs are forced graphs on the full ambient board, including isolates.
-/

namespace GridGraphs.RailRepair

open Finset SimpleGraph BoundaryFiveConstruction BoundaryFiveFrame
open ResidueTwoStaircase (Vertex interval mem_interval Footprint)

noncomputable section
attribute [local instance] Classical.propDecidable

def right (s : ℕ) (j : Fin s) : Finset (Vertex s) :=
  interval s (3 * j.val + 3) (if j.val + 1 = s then s + 6 else j.val + 4)
    (3 * s + 2)

abbrev BaseIndex (s : ℕ) := Unit ⊕ Fin s ⊕ Fin (s - 1)

def basePiece (s : ℕ) : BaseIndex s → Finset (Vertex s)
  | .inl _ => interval s 2 2 2
  | .inr (.inl j) => right s j
  | .inr (.inr j) => ResidueTwoStaircase.L s j

def base (s : ℕ) : Finset (Vertex s) := univ.biUnion (basePiece s)

abbrev NewIndex (s : ℕ) := Unit ⊕ Unit ⊕ Unit ⊕ Fin ((s - 2) / 2)

/-- U, V, W, and the alternating reduced pocket X, respectively. -/
def newPiece (s : ℕ) : NewIndex s → Finset (Vertex s)
  | .inl _ => interval s (3 * s - 1) (s + 4) (s + 4)
  | .inr (.inl _) => interval s (3 * s + 1) (s + 1) (s + 3)
  | .inr (.inr (.inl _)) => interval s (3 * s + 2) (s + 5) (s + 5)
  | .inr (.inr (.inr t)) =>
      interval s (3 * s + 2 - t.val % 2) (s - 1 - 2 * t.val) (s - 1 - 2 * t.val)

def repaired (s : ℕ) : Finset (Vertex s) := base s ∪ univ.biUnion (newPiece s)

def baseFootprint (s : ℕ) : BaseIndex s → Set (Vertex s)
  | .inl _ => Footprint 2 2 2
  | .inr (.inl j) =>
      Footprint (3 * j.val + 3) (if j.val + 1 = s then s + 6 else j.val + 4) (3 * s + 2)
  | .inr (.inr j) => Footprint (3 * j.val + 5) 2 (j.val + 3)

def newFootprint (s : ℕ) : NewIndex s → Set (Vertex s)
  | .inl _ => Footprint (3 * s - 1) (s + 4) (s + 4)
  | .inr (.inl _) => Footprint (3 * s + 1) (s + 1) (s + 3)
  | .inr (.inr (.inl _)) => Footprint (3 * s + 2) (s + 5) (s + 5)
  | .inr (.inr (.inr t)) =>
      Footprint (3 * s + 2 - t.val % 2) (s - 1 - 2 * t.val) (s - 1 - 2 * t.val)

theorem base_support_subset (s : ℕ) (i : BaseIndex s) :
    (J (basePiece s i)).support ⊆ baseFootprint s i := by
  intro v hv
  rcases i with u | j | j <;> exact ResidueTwoStaircase.interval_support hv

theorem new_support_subset (s : ℕ) (i : NewIndex s) :
    (J (newPiece s i)).support ⊆ newFootprint s i := by
  intro v hv
  rcases i with u | u | u | t <;> exact ResidueTwoStaircase.interval_support hv

theorem new_isAcyclic (s : ℕ) (i : NewIndex s) : (J (newPiece s i)).IsAcyclic := by
  rcases i with u | u | u | t <;> exact ResidueTwoStaircase.interval_isAcyclic _ _ _ _

theorem base_subset_source (s : ℕ) : base s ⊆ ResidueTwoStaircase.A s := by
  intro v hv
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
  rw [ResidueTwoStaircase.mem_A]
  rcases i with u | j | j
  · left
    simp only [basePiece, mem_interval] at hi
    exact Prod.ext (Fin.ext hi.1) (Fin.ext (by dsimp [ResidueTwoStaircase.z]; omega))
  · right; left
    refine ⟨j, ?_⟩
    simp only [basePiece, right, mem_interval] at hi
    simp only [ResidueTwoStaircase.R, mem_interval]
    split_ifs at hi <;> have := j.isLt <;> omega
  · exact Or.inr (Or.inr (Or.inl ⟨j, hi⟩))

theorem repaired_subset_Deep {s : ℕ} (hs : 2 ≤ s) :
    (↑(repaired s) : Set (Vertex s)) ⊆ Deep (3 * s + 5) := by
  intro v hv
  rcases mem_union.mp hv with hb | hn
  · exact ResidueTwoStaircase.A_subset_Deep hs (base_subset_source s hb)
  · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hn
    rcases i with u | u | u | t <;>
      simp only [newPiece, mem_interval] at hi <;> dsimp [Deep] <;> omega

/-- Supports of the new pieces are mutually disjoint, including nonempty pockets. -/
theorem new_footprints_disjoint {s : ℕ} (hs : 2 ≤ s) :
    Pairwise (fun i j => Disjoint (newFootprint s i) (newFootprint s j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hi hj
  change newFootprint s i v at hi
  change newFootprint s j v at hj
  rcases i with u | u | u | t <;> rcases j with w | w | w | q <;>
    simp only [newFootprint, Footprint] at hi hj
  all_goals simp only [ne_eq, Sum.inr.injEq, Fin.ext_iff] at hij
  all_goals first | exact hij trivial | omega

/-- The possible attachment coordinates, not a claim of connectedness. -/
def Attachment (s : ℕ) : NewIndex s → Vertex s → Prop
  | .inl _, v => v.1.val = 3 * s - 2 ∧ v.2.val = s + 4
  | .inr (.inl _), v => v.1.val = 3 * s ∧ v.2.val = s + 1
  | .inr (.inr (.inl _)), v => v.1.val = 3 * s + 3 ∧ v.2.val = s + 5
  | .inr (.inr (.inr t)), v =>
      v.1.val = (if t.val % 2 = 0 then 3 * s + 3 else 3 * s) ∧
      v.2.val = s - 1 - 2 * t.val

theorem new_base_inter_location {s : ℕ} (hs : 2 ≤ s)
    (i : NewIndex s) (j : BaseIndex s) {v : Vertex s}
    (hi : v ∈ newFootprint s i) (hj : v ∈ baseFootprint s j) : Attachment s i v := by
  change newFootprint s i v at hi
  change baseFootprint s j v at hj
  rcases i with u | u | u | t <;> rcases j with w | j | j <;>
    simp only [newFootprint, baseFootprint, Footprint, Attachment] at hi hj ⊢
  all_goals (try split_ifs at *) <;> omega

theorem new_frame_inter_location {s : ℕ} (hs : 2 ≤ s)
    (i : NewIndex s) {v : Vertex s}
    (hi : v ∈ newFootprint s i) (hf : v ∈ (Houter (3 * s + 5)).support) :
    Attachment s i v := by
  have hf := ((BoundaryFiveFrame.mem_support_iff (by omega) v).mp hf).1
  simp only [IsGridBoundary, NextRing] at hf
  change newFootprint s i v at hi
  rcases i with u | u | u | t <;>
    simp only [newFootprint, Footprint, Attachment] at hi ⊢
  all_goals (try split_ifs) <;> omega

theorem attachment_subsingleton (s : ℕ) (i : NewIndex s) :
    {v | Attachment s i v}.Subsingleton := by
  intro v hv w hw
  rcases i with u | u | u | t <;>
    simp only [Set.mem_ofPred_eq, Attachment] at hv hw <;>
    exact Prod.ext (Fin.ext (hv.1.trans hw.1.symm)) (Fin.ext (hv.2.trans hw.2.symm))

end
end GridGraphs.RailRepair
