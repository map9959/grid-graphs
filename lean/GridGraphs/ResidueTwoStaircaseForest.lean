import GridGraphs.ResidueTwoStaircase
import GridGraphs.IntervalStarGluing

/-! # The improved residue-two staircase is a forced forest -/

namespace GridGraphs.ResidueTwoStaircase

open Finset SimpleGraph BoundaryFiveConstruction BoundaryFiveFrame

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A horizontal interval has only pendant vertices off its row. -/
theorem interval_isAcyclic (s r a b : ℕ) :
    (J (interval s r a b)).IsAcyclic := by
  classical
  intro v c hc
  have onRow (x : Vertex s) (hx : x ∈ c.support) : x.1.val = r := by
    let d := c.rotate x hx
    have hd : d.IsCycle := hc.rotate hx
    have h1 := d.adj_snd hd.not_nil
    have h2 := (d.adj_penultimate hd.not_nil).symm
    by_contra hr
    have unique (y z : Vertex s) (hy : (J (interval s r a b)).Adj x y)
        (hz : (J (interval s r a b)).Adj x z) : y = z := by
      simp only [J, forcedEdgeGraph, gridGraph, adjacent, Fin.ext_iff,
        mem_coe, mem_interval] at hy hz
      apply Prod.ext <;> apply Fin.ext <;> omega
    exact hd.snd_ne_penultimate (unique _ _ h1 h2)
  obtain ⟨x, hx, hmax⟩ := c.support.toFinset.exists_max_image (fun x => x.2.val)
    ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  have hx' := List.mem_toFinset.mp hx
  let d := c.rotate x hx'
  have hd : d.IsCycle := hc.rotate hx'
  have hs : d.snd ∈ c.support :=
    (c.mem_support_rotate_iff x hx').mp (d.getVert_mem_support 1)
  have ht : d.penultimate ∈ c.support :=
    (c.mem_support_rotate_iff x hx').mp (d.getVert_mem_support (d.length - 1))
  have hsr := onRow _ hs
  have htr := onRow _ ht
  have hxr := onRow _ hx'
  have hsm := hmax _ (List.mem_toFinset.mpr hs)
  have htm := hmax _ (List.mem_toFinset.mpr ht)
  have ha := (d.adj_snd hd.not_nil).1
  have hb := (d.adj_penultimate hd.not_nil).1
  simp only [gridGraph, adjacent, Fin.ext_iff] at ha hb
  apply hd.snd_ne_penultimate
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- The cross-shaped support envelope of a horizontal interval. -/
def Footprint (r a b : ℕ) (v : Vertex s) : Prop :=
  (v.1.val = r ∧ a ≤ v.2.val + 1 ∧ v.2.val ≤ b + 1) ∨
    ((v.1.val + 1 = r ∨ r + 1 = v.1.val) ∧ a ≤ v.2.val ∧ v.2.val ≤ b)

theorem interval_support {s r a b : ℕ} {v : Vertex s}
    (hv : v ∈ (J (interval s r a b)).support) : Footprint r a b v := by
  obtain ⟨w, hw⟩ := hv
  change (J (interval s r a b)).Adj v w at hw
  simp only [J, forcedEdgeGraph, gridGraph, adjacent, Fin.ext_iff,
    mem_coe, mem_interval] at hw
  unfold Footprint
  omega

private theorem z_interval (s : ℕ) : {z s} = interval s 2 2 2 := by
  ext v
  simp only [mem_singleton, mem_interval, Prod.ext_iff, Fin.ext_iff, z]
  omega

theorem piece_isAcyclic (s : ℕ) (i : Index s) : (J (piece s i)).IsAcyclic := by
  rcases i with u | j | j | t | t
  · simpa only [piece, z_interval] using interval_isAcyclic s 2 2 2
  · exact interval_isAcyclic _ _ _ _
  · exact interval_isAcyclic _ _ _ _
  · exact interval_isAcyclic _ _ _ _
  · exact interval_isAcyclic _ _ _ _

def footprint (s : ℕ) : Index s → Set (Vertex s)
  | .inl _ => Footprint 2 2 2
  | .inr (.inl j) => Footprint (3 * j.val + 3) (j.val + 4) (3 * s + 2)
  | .inr (.inr (.inl j)) => Footprint (3 * j.val + 5) 2 (j.val + 3)
  | .inr (.inr (.inr (.inl t))) =>
      Footprint (3 * s + 2) (s + 2 - 4 * t.val) (s + 2 - 4 * t.val)
  | .inr (.inr (.inr (.inr t))) =>
      Footprint (3 * s + 1) (s - 4 * t.val) (s - 4 * t.val)

theorem piece_support_subset (s : ℕ) (i : Index s) :
    (J (piece s i)).support ⊆ footprint s i := by
  intro v hv
  rcases i with u | j | j | t | t
  · simp only [piece, z_interval] at hv
    exact interval_support hv
  · exact interval_support hv
  · exact interval_support hv
  · exact interval_support hv
  · exact interval_support hv

def IsBase {s : ℕ} : Index s → Prop
  | .inr (.inr (.inr (.inr _))) => False
  | _ => True

def baseIndices (s : ℕ) : Finset (Index s) := univ.filter IsBase

/-- Distinct baseline stars have no physical vertex in common. -/
theorem base_footprints_disjoint {s : ℕ} (hs : 2 ≤ s) {i k : Index s}
    (hi : IsBase i) (hk : IsBase k) (hne : i ≠ k) :
    Disjoint (footprint s i) (footprint s k) := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  change footprint s i v at hv
  change footprint s k v at hw
  rcases i with u | j | j | t | t <;>
    rcases k with w | l | l | q | q <;>
    simp only [IsBase] at hi hk
  all_goals try contradiction
  all_goals simp only [footprint, Footprint] at hv hw
  all_goals simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff] at hne
  all_goals first | exact hne trivial | omega

/-- A P star can meet a distinct piece only at its upper neighbor. -/
theorem P_footprint_inter {s : ℕ} (hs : 2 ≤ s)
    (t : Fin ((s + 1) / 4)) {i : Index s}
    (hne : i ≠ .inr (.inr (.inr (.inr t)))) {v : Vertex s}
    (hv : v ∈ footprint s i)
    (hw : Footprint (3 * s + 1) (s - 4 * t.val) (s - 4 * t.val) v) :
    v.1.val = 3 * s ∧ v.2.val = s - 4 * t.val := by
  change footprint s i v at hv
  rcases i with u | j | j | q | q <;>
    simp only [footprint, Footprint] at hv hw
  all_goals simp only [ne_eq, Sum.inr.injEq, Fin.ext_iff] at hne
  all_goals omega

private theorem frame_footprint {s : ℕ} (hs : 2 ≤ s) {v : Vertex s}
    (hv : v ∈ (Houter (3 * s + 5)).support) :
    (IsGridBoundary v ∨ NextRing v) ∧ ¬ (v.1.val = 1 ∧ v.2.val = 2) := by
  obtain ⟨hb, hw⟩ := (BoundaryFiveFrame.mem_support_iff (by omega) v).mp hv
  refine ⟨hb, ?_⟩
  intro h
  apply hw
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- Each baseline piece has at most one attachment to the actual frame. -/
theorem base_frame_inter {s : ℕ} (hs : 2 ≤ s) (i : Index s) (hi : IsBase i) :
    ((Houter (3 * s + 5)).support ∩ footprint s i).Subsingleton := by
  intro v hv w hw
  have hvf := frame_footprint hs hv.1
  have hwf := frame_footprint hs hw.1
  have hvp := hv.2
  have hwp := hw.2
  change footprint s i v at hvp
  change footprint s i w at hwp
  rcases i with u | j | j | t | t <;> simp only [IsBase] at hi
  all_goals simp only [footprint, Footprint] at hvp hwp
  all_goals simp only [IsGridBoundary, NextRing] at hvf hwf
  all_goals apply Prod.ext <;> apply Fin.ext <;> omega

theorem P_frame_disjoint {s : ℕ} (hs : 2 ≤ s) (t : Fin ((s + 1) / 4)) :
    Disjoint (Houter (3 * s + 5)).support
      (footprint s (.inr (.inr (.inr (.inr t))))) := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  have hf := frame_footprint hs hv
  change footprint s (.inr (.inr (.inr (.inr t)))) v at hw
  simp only [IsGridBoundary, NextRing] at hf
  simp only [footprint, Footprint] at hw
  omega

/-- The actual frame together with a finite selection of staircase pieces. -/
def familyGraph (s : ℕ) (S : Finset (Index s)) : SimpleGraph (Vertex s) :=
  Houter (3 * s + 5) ⊔ J (S.biUnion (piece s))

theorem biUnion_support {s : ℕ} (S : Finset (Index s)) (v : Vertex s) :
    v ∈ (J (S.biUnion (piece s))).support ↔
      ∃ i ∈ S, v ∈ (J (piece s i)).support := by
  constructor
  · rintro ⟨w, hw⟩
    change (J (S.biUnion (piece s))).Adj v w at hw
    rcases hw with ⟨ha, hv | hw⟩
    · obtain ⟨i, hi, hv⟩ := mem_biUnion.mp hv
      exact ⟨i, hi, w, ha, Or.inl hv⟩
    · obtain ⟨i, hi, hw⟩ := mem_biUnion.mp hw
      exact ⟨i, hi, w, ha, Or.inr hw⟩
  · rintro ⟨i, hi, w, hw⟩
    change (J (piece s i)).Adj v w at hw
    refine ⟨w, hw.1, ?_⟩
    rcases hw.2 with hv | hw
    · exact Or.inl (mem_biUnion.mpr ⟨i, hi, hv⟩)
    · exact Or.inr (mem_biUnion.mpr ⟨i, hi, hw⟩)

theorem familyGraph_insert (s : ℕ) (S : Finset (Index s)) (i : Index s) :
    familyGraph s (insert i S) = J (piece s i) ⊔ familyGraph s S := by
  ext v w
  simp only [familyGraph, J, sup_adj, forcedEdgeGraph, biUnion_insert,
    mem_coe, mem_union]
  tauto

theorem base_family_isAcyclic {s : ℕ} (hs : 2 ≤ s) (S : Finset (Index s))
    (hS : ∀ i ∈ S, IsBase i) : (familyGraph s S).IsAcyclic := by
  induction S using Finset.induction_on with
  | empty =>
      have he : familyGraph s ∅ = Houter (3 * s + 5) := by
        ext v w
        simp [familyGraph, J, forcedEdgeGraph]
      rw [he]
      exact Houter_isAcyclic (by omega)
  | @insert i S hi ih =>
      have hib := hS i (mem_insert_self _ _)
      have hSb : ∀ k ∈ S, IsBase k := fun k hk => hS k (mem_insert_of_mem hk)
      rw [familyGraph_insert]
      apply (piece_isAcyclic s i).sup_of_support_inter_subsingleton (ih hSb)
      have onlyFrame {v : Vertex s}
          (hv : v ∈ (J (piece s i)).support ∩ (familyGraph s S).support) :
          v ∈ (Houter (3 * s + 5)).support := by
        rcases (support_sup _ _ ▸ hv.2) with hf | hu
        · exact hf
        · obtain ⟨k, hk, hvk⟩ := (biUnion_support S v).mp hu
          have hne : i ≠ k := by intro he; exact hi (he ▸ hk)
          exact False.elim (Set.disjoint_left.mp
            (base_footprints_disjoint hs hib (hSb k hk) hne)
            (piece_support_subset s i hv.1) (piece_support_subset s k hvk))
      intro v hv w hw
      exact base_frame_inter hs i hib
        ⟨onlyFrame hv, piece_support_subset s i hv.1⟩
        ⟨onlyFrame hw, piece_support_subset s i hw.1⟩

/-- Every P star attaches at most once, even after any other pieces were added. -/
theorem insert_P_isAcyclic {s : ℕ} (hs : 2 ≤ s) (S : Finset (Index s))
    (t : Fin ((s + 1) / 4))
    (ht : Sum.inr (Sum.inr (Sum.inr (Sum.inr t))) ∉ S)
    (hS : (familyGraph s S).IsAcyclic) :
    (familyGraph s (insert (.inr (.inr (.inr (.inr t)))) S)).IsAcyclic := by
  rw [familyGraph_insert]
  apply (piece_isAcyclic s _).sup_of_support_inter_subsingleton hS
  have location {v : Vertex s}
      (hv : v ∈ (J (piece s (.inr (.inr (.inr (.inr t)))))).support ∩
        (familyGraph s S).support) :
      v.1.val = 3 * s ∧ v.2.val = s - 4 * t.val := by
    have hp := piece_support_subset s _ hv.1
    rcases (support_sup _ _ ▸ hv.2) with hf | hu
    · exact False.elim (Set.disjoint_left.mp (P_frame_disjoint hs t) hf hp)
    · obtain ⟨i, hi, hvi⟩ := (biUnion_support S v).mp hu
      have hne : i ≠ .inr (.inr (.inr (.inr t))) := by
        intro he
        exact ht (he ▸ hi)
      exact P_footprint_inter hs t hne (piece_support_subset s i hvi) hp
  intro v hv w hw
  have hv' := location hv
  have hw' := location hw
  exact Prod.ext (Fin.ext (hv'.1.trans hw'.1.symm))
    (Fin.ext (hv'.2.trans hw'.2.symm))

/-- Baseline first, then P: the entire concrete staircase and frame are acyclic. -/
theorem family_isAcyclic {s : ℕ} (hs : 2 ≤ s) (S : Finset (Index s)) :
    (familyGraph s (baseIndices s ∪ S)).IsAcyclic := by
  induction S using Finset.induction_on with
  | empty =>
      rw [union_empty]
      exact base_family_isAcyclic hs _ (fun i hi => (mem_filter.mp hi).2)
  | @insert i S hi ih =>
      rw [union_insert]
      by_cases hm : i ∈ baseIndices s ∪ S
      · rwa [insert_eq_of_mem hm]
      · have hn : ¬ IsBase i := by
          intro hb
          exact hm (mem_union_left _ (mem_filter.mpr ⟨mem_univ i, hb⟩))
        rcases i with u | j | j | t | t <;> simp only [IsBase, not_true_eq_false] at hn
        exact insert_P_isAcyclic hs _ t hm ih

theorem Ffull_isAcyclic {s : ℕ} (hs : 2 ≤ s) :
    (forcedEdgeGraph (gridGraph (3 * s + 5) (3 * s + 5))
      (↑(Ffull (A s)) : Set (Vertex s))).IsAcyclic := by
  rw [forcedEdgeGraph_Ffull]
  have h := family_isAcyclic hs univ
  have he : baseIndices s ∪ (univ : Finset (Index s)) = univ := by
    ext i
    simp
  rw [he] at h
  exact h

theorem Ffull_card {s : ℕ} (hs : 2 ≤ s) :
    (Ffull (A s)).card = 3 * s ^ 2 + 12 * s + 11 + (s + 1) / 2 := by
  rw [BoundaryFiveConstruction.Ffull_card (by omega) (A_subset_Deep hs), A_card hs]
  omega

theorem staircase_le_maxPreserved {s : ℕ} (hs : 2 ≤ s) :
    3 * s ^ 2 + 12 * s + 11 + (s + 1) / 2 ≤
      maxPreserved (3 * s + 5) (3 * s + 5) := by
  rw [← Ffull_card hs, maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  exact Finset.le_sup (f := Finset.card) (mem_acyclicForcedSets.mpr (Ffull_isAcyclic hs))

theorem residueTwo_le_maxPreserved {k : ℕ} (hk : 3 ≤ k) :
    3 * k ^ 2 + 6 * k + 2 + k / 2 ≤ maxPreserved (3 * k + 2) (3 * k + 2) := by
  have h := staircase_le_maxPreserved (s := k - 1) (by omega)
  have he : 3 * (k - 1) + 5 = 3 * k + 2 := by omega
  have hk' : k - 1 + 1 = k := by omega
  rw [he, hk'] at h
  have hc : 3 * (k - 1) ^ 2 + 12 * (k - 1) + 11 = 3 * k ^ 2 + 6 * k + 2 := by
    nlinarith
  rwa [hc] at h

/-- Exact remaining deficit from the conjectured stable target. -/
theorem stable_target_eq_staircase_add_gap {k : ℕ} (hk : 5 ≤ k) :
    3 * k ^ 2 + 7 * k =
      (3 * k ^ 2 + 6 * k + 2 + k / 2) + ((k - 1) / 2 - 1) := by
  omega

end

end GridGraphs.ResidueTwoStaircase
