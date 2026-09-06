import GridGraphs.Constructions.BoundaryFive.BoundaryFiveAttachment
import GridGraphs.Core.ForcedMaximum

/-! # Counted extension by the normalized boundary-five frame

The inner input lives on the original board. This constructs and counts its
union with the actual outer frame; it does not assert existence of an inner
input of the required size and attachment pattern.
-/

namespace GridGraphs.BoundaryFiveConstruction

open SimpleGraph BoundaryFiveFrame BoundaryFiveAttachment

local notation "I" => BoundaryFiveAttachment.I

attribute [local instance] Classical.propDecidable

/-- The twice-cropped square in ambient, zero-based coordinates. -/
def Deep (n : Nat) : Set (GridVertex n n) :=
  {v | 2 ≤ v.1.val ∧ v.1.val ≤ n - 3 ∧
    2 ≤ v.2.val ∧ v.2.val ≤ n - 3}

def J {n : Nat} (A : Finset (GridVertex n n)) : SimpleGraph (GridVertex n n) :=
  forcedEdgeGraph (gridGraph n n) (↑A : Set (GridVertex n n))

noncomputable def Ffull {n : Nat} (A : Finset (GridVertex n n)) :
    Finset (GridVertex n n) :=
  (Fouter n).toFinset ∪ A

/-- Every incident edge, not just edges between selected vertices, stays in I. -/
theorem J_adj_inside {n : Nat} (hn : 7 ≤ n) {A : Finset (GridVertex n n)}
    (hA : (↑A : Set (GridVertex n n)) ⊆ Deep n) {x y : GridVertex n n}
    (h : (J A).Adj x y) : x ∈ I n ∧ y ∈ I n := by
  rcases h with ⟨hadj, hx | hy⟩
  · have hx := hA hx
    simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
    dsimp [Deep, BoundaryFiveAttachment.I] at hx ⊢
    omega
  · have hy := hA hy
    simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
    dsimp [Deep, BoundaryFiveAttachment.I] at hy ⊢
    omega

theorem forcedEdgeGraph_Ffull {n : Nat} (A : Finset (GridVertex n n)) :
    forcedEdgeGraph (gridGraph n n) (↑(Ffull A) : Set (GridVertex n n)) =
      Houter n ⊔ J A := by
  classical
  ext x y
  simp only [forcedEdgeGraph, Ffull, Finset.mem_coe, Finset.mem_union,
    Set.mem_toFinset, sup_adj, Houter, J]
  tauto

/-- Exact feasibility criterion for the concrete union. -/
theorem Ffull_isAcyclic_iff {n : Nat} (hn : 7 ≤ n)
    {A : Finset (GridVertex n n)} (hA : (↑A : Set (GridVertex n n)) ⊆ Deep n) :
    (forcedEdgeGraph (gridGraph n n) (↑(Ffull A) : Set (GridVertex n n))).IsAcyclic ↔
      (J A).IsAcyclic ∧
        ∀ x ∈ (Houter n).support ∩ I n,
          ∀ y ∈ (Houter n).support ∩ I n, (J A).Reachable x y → x = y := by
  rw [forcedEdgeGraph_Ffull]
  exact Houter_sup_isAcyclic_iff hn (J A) (fun ⦃_ _⦄ h => J_adj_inside hn hA h)

/-- Count the actual boundary using the concrete clockwise rank bijection. -/
theorem boundary_card {n : Nat} (hn : 7 ≤ n) :
    (({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset).card = 4 * n - 4 := by
  classical
  rw [← Finset.card_range (4 * n - 4)]
  apply Finset.card_bij (fun v _ => boundaryRank v)
  · intro v hv
    exact Finset.mem_range.mpr (boundaryRank_lt hn v (by simpa using hv))
  · intro v hv p hp he
    exact boundaryRank_injective hn (by simpa using hv) (by simpa using hp) he
  · intro k hk
    obtain ⟨v, hv, he⟩ := exists_boundaryRank hn k (Finset.mem_range.mp hk)
    exact ⟨v, by simpa using hv, he⟩

/-- The holes are five distinct, explicit boundary coordinates. -/
theorem holes_card {n : Nat} (hn : 7 ≤ n) :
    (({v | BoundaryHole v} : Set (GridVertex n n)).toFinset).card = 5 := by
  classical
  let a : GridVertex n n := (⟨0, by omega⟩, ⟨1, by omega⟩)
  let b : GridVertex n n := (⟨0, by omega⟩, ⟨2, by omega⟩)
  let c : GridVertex n n := (⟨1, by omega⟩, ⟨n - 1, by omega⟩)
  let d : GridVertex n n := (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)
  let e : GridVertex n n := (⟨n - 2, by omega⟩, ⟨0, by omega⟩)
  have heq : ({v | BoundaryHole v} : Set (GridVertex n n)).toFinset = {a, b, c, d, e} := by
    apply Finset.ext
    intro v
    rw [Set.mem_toFinset]
    simp only [Set.mem_ofPred_eq, BoundaryHole, Finset.mem_insert,
      Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff, a, b, c, d, e]
    omega
  rw [heq]
  have h1 : n - 1 ≠ 0 := by omega
  have h2 : n - 2 ≠ 0 := by omega
  have h3 : n - 1 ≠ 1 := by omega
  have h4 : n - 2 ≠ 1 := by omega
  have h5 : n - 1 ≠ n - 2 := by omega
  simp [a, b, c, d, e, Prod.ext_iff, Fin.ext_iff, h1, h2, h5,
    Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

theorem Fouter_card {n : Nat} (hn : 7 ≤ n) :
    (Fouter n).toFinset.card = 4 * n - 9 := by
  classical
  have hsub : ({v | BoundaryHole v} : Set (GridVertex n n)).toFinset ⊆
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset := by
    intro v hv
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hv ⊢
    unfold BoundaryHole at hv
    unfold IsGridBoundary
    omega
  have heq : (Fouter n).toFinset =
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset \
        ({v | BoundaryHole v} : Set (GridVertex n n)).toFinset := by
    apply Finset.ext
    intro v
    rw [Finset.mem_sdiff, Set.mem_toFinset, Set.mem_toFinset, Set.mem_toFinset]
    rfl
  rw [heq, Finset.card_sdiff_of_subset hsub, boundary_card hn, holes_card hn]
  omega

theorem Fouter_disjoint {n : Nat} (hn : 7 ≤ n) {A : Finset (GridVertex n n)}
    (hA : (↑A : Set (GridVertex n n)) ⊆ Deep n) :
    Disjoint (Fouter n).toFinset A := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hvA
  have hb := (Set.mem_toFinset.mp hv).1
  have hd := hA hvA
  unfold IsGridBoundary at hb
  dsimp [Deep] at hd
  omega

theorem Ffull_card {n : Nat} (hn : 7 ≤ n) {A : Finset (GridVertex n n)}
    (hA : (↑A : Set (GridVertex n n)) ⊆ Deep n) :
    (Ffull A).card = 4 * n - 9 + A.card := by
  classical
  rw [Ffull, Finset.card_union_of_disjoint (Fouter_disjoint hn hA), Fouter_card hn]

/-- Concrete counted extension: inner feasibility and attachment suffice. -/
theorem counted_extension {n : Nat} (hn : 7 ≤ n) {A : Finset (GridVertex n n)}
    (hA : (↑A : Set (GridVertex n n)) ⊆ Deep n) (hJ : (J A).IsAcyclic)
    (hattach : ∀ x ∈ (Houter n).support ∩ I n,
      ∀ y ∈ (Houter n).support ∩ I n, (J A).Reachable x y → x = y) :
    (forcedEdgeGraph (gridGraph n n) (↑(Ffull A) : Set (GridVertex n n))).IsAcyclic ∧
      (Ffull A).card = 4 * n - 9 + A.card :=
  ⟨(Ffull_isAcyclic_iff hn hA).mpr ⟨hJ, hattach⟩, Ffull_card hn hA⟩

theorem counted_le_maxPreserved {n : Nat} (hn : 7 ≤ n)
    {A : Finset (GridVertex n n)} (hA : (↑A : Set (GridVertex n n)) ⊆ Deep n)
    (hJ : (J A).IsAcyclic)
    (hattach : ∀ x ∈ (Houter n).support ∩ I n,
      ∀ y ∈ (Houter n).support ∩ I n, (J A).Reachable x y → x = y) :
    4 * n - 9 + A.card ≤ maxPreserved n n := by
  obtain ⟨hf, hc⟩ := counted_extension hn hA hJ hattach
  rw [← hc, maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  exact Finset.le_sup (f := Finset.card) (mem_acyclicForcedSets.mpr hf)

/-- Subtraction-free size interface for any desired target. -/
theorem target_le_maxPreserved {n target : Nat} (hn : 7 ≤ n)
    {A : Finset (GridVertex n n)} (hA : (↑A : Set (GridVertex n n)) ⊆ Deep n)
    (hJ : (J A).IsAcyclic)
    (hattach : ∀ x ∈ (Houter n).support ∩ I n,
      ∀ y ∈ (Houter n).support ∩ I n, (J A).Reachable x y → x = y)
    (hcard : A.card + 4 * n = target + 9) : target ≤ maxPreserved n n := by
  have h := counted_le_maxPreserved hn hA hJ hattach
  omega

/-- The residue-two target remains conditional on a genuine inner input. -/
theorem residueTwo_le_maxPreserved {k : Nat} (hk : 7 ≤ k)
    {A : Finset (GridVertex (3 * k + 2) (3 * k + 2))}
    (hA : (↑A : Set (GridVertex (3 * k + 2) (3 * k + 2))) ⊆ Deep (3 * k + 2))
    (hJ : (J A).IsAcyclic)
    (hattach : ∀ x ∈ (Houter (3 * k + 2)).support ∩ I (3 * k + 2),
      ∀ y ∈ (Houter (3 * k + 2)).support ∩ I (3 * k + 2),
        (J A).Reachable x y → x = y)
    (hcard : A.card = 3 * k ^ 2 - 5 * k + 1) :
    3 * k ^ 2 + 7 * k ≤ maxPreserved (3 * k + 2) (3 * k + 2) := by
  apply target_le_maxPreserved (by omega) hA hJ hattach
  have hle : 5 * k ≤ 3 * k ^ 2 := by nlinarith
  rw [hcard]
  omega

end GridGraphs.BoundaryFiveConstruction
