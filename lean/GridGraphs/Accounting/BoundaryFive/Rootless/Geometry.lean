import GridGraphs.Accounting.CarrierLengthBound
import GridGraphs.Accounting.BoundaryStratifiedCarrierBound

/-!
# Actual deep-root geometry

All coordinates here belong to the deep square itself, starting at zero.
`UniqueBoundaryRoots` is a condition on reachability in the actual forced
graph, not on induced carriers. No ambient connectivity or canonical frame
is assumed. Deriving this condition from the ambient c=2 profile is a
separate obligation.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

def UniqueBoundaryRoots {m : Nat} (F : Set (GridVertex m m)) : Prop :=
  ∀ u ∈ F, ∀ v ∈ F, IsGridBoundary u → IsGridBoundary v →
    (forcedEdgeGraph (gridGraph m m) F).Reachable u v → u = v

/-- Every forced component, including any putative isolate, has a preserved
boundary root. This does NOT say that the forced graph is connected. -/
def BoundaryRooted {m : Nat} (F : Set (GridVertex m m)) : Prop :=
  ∀ v, ∃ u ∈ F, IsGridBoundary u ∧
    (forcedEdgeGraph (gridGraph m m) F).Reachable v u

theorem boundary_rooted_dominated {m : Nat} {F : Set (GridVertex m m)}
    (hroot : BoundaryRooted F) (v : GridVertex m m) (hv : v ∉ F) :
    ∃ u ∈ F, (gridGraph m m).Adj v u := by
  obtain ⟨u, hu, _, ⟨p⟩⟩ := hroot v
  cases p with
  | nil => exact (hv hu).elim
  | cons h _ => exact ⟨_, h.2.resolve_left hv, h.1⟩

/-- A U corner is covered by exactly one of its two adjacent boundary roots.
Both alternatives are retained; no orientation of a different hole is fixed. -/
theorem top_left_corner_root {m : Nat} (hm : 2 ≤ m)
    {F : Set (GridVertex m m)}
    (hex : BoundaryRooted F) (hroot : UniqueBoundaryRoots F)
    (hz : (⟨0, by omega⟩, ⟨0, by omega⟩) ∉ F) :
    ((⟨1, by omega⟩, ⟨0, by omega⟩) ∈ F ∨
      (⟨0, by omega⟩, ⟨1, by omega⟩) ∈ F) ∧
    ¬ ((⟨1, by omega⟩, ⟨0, by omega⟩) ∈ F ∧
      (⟨0, by omega⟩, ⟨1, by omega⟩) ∈ F) := by
  constructor
  · obtain ⟨u, hu, hadj⟩ := boundary_rooted_dominated hex _ hz
    have hc := hadj
    simp only [gridGraph, adjacent, Fin.ext_iff] at hc
    have he : u = (⟨1, by omega⟩, ⟨0, by omega⟩) ∨
        u = (⟨0, by omega⟩, ⟨1, by omega⟩) := by
      simp only [Prod.ext_iff, Fin.ext_iff]
      dsimp at hc
      omega
    rcases he with rfl | rfl
    · exact Or.inl hu
    · exact Or.inr hu
  · rintro ⟨hl, ht⟩
    have h1 : (forcedEdgeGraph (gridGraph m m) F).Adj
        (⟨1, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨0, by omega⟩) :=
      ⟨by simp [gridGraph, adjacent], Or.inl hl⟩
    have h2 : (forcedEdgeGraph (gridGraph m m) F).Adj
        (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨1, by omega⟩) :=
      ⟨by simp [gridGraph, adjacent], Or.inr ht⟩
    have he := hroot _ hl _ ht (by simp [IsGridBoundary]) (by simp [IsGridBoundary])
      (h1.reachable.trans h2.reachable)
    have := congrArg (fun x : GridVertex m m => x.1.val) he
    simp at this

theorem induced_reachable_forced {m : Nat} {F : Set (GridVertex m m)}
    {u v : F} (h : ((gridGraph m m).induce F).Reachable u v) :
    (forcedEdgeGraph (gridGraph m m) F).Reachable u.1 v.1 := by
  let f : ((gridGraph m m).induce F) →g forcedEdgeGraph (gridGraph m m) F :=
    ⟨Subtype.val, fun {a _} h => ⟨h, Or.inl a.2⟩⟩
  exact h.map f

/-- A full-length straight carrier would contain two boundary roots. -/
theorem strict_carrier_cap {m : Nat} (hm : 2 ≤ m)
    {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (hroot : UniqueBoundaryRoots F)
    (C : ((gridGraph m m).induce F).ConnectedComponent) :
    C.supp.ncard ≤ m - 1 := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · let f : C.supp → Fin m := fun v => v.1.1.2
    have hi : Function.Injective f := by
      intro v w h
      exact Subtype.ext (Subtype.ext (Prod.ext ((hr _ v.2).trans (hr _ w.2).symm) h))
    have hn : ¬ Function.Surjective f := by
      intro hs
      obtain ⟨u, hu⟩ := hs ⟨0, by omega⟩
      obtain ⟨v, hv⟩ := hs ⟨m - 1, by omega⟩
      have he := hroot u.1.1 u.1.2 v.1.1 v.1.2
        (by right; right; left; exact congrArg Fin.val hu)
        (by right; right; right; have := congrArg Fin.val hv; dsimp [f] at this; omega)
        (induced_reachable_forced (C.reachable_of_mem_supp u.2 v.2))
      have := congrArg (fun x : GridVertex m m => x.2.val) he
      have hu' := congrArg Fin.val hu
      have hv' := congrArg Fin.val hv
      dsimp [f] at hu' hv'
      omega
    have := Fintype.card_lt_of_injective_not_surjective f hi hn
    simp only [Fintype.card_fin] at this
    omega
  · let f : C.supp → Fin m := fun v => v.1.1.1
    have hi : Function.Injective f := by
      intro v w h
      exact Subtype.ext (Subtype.ext (Prod.ext h ((hc _ v.2).trans (hc _ w.2).symm)))
    have hn : ¬ Function.Surjective f := by
      intro hs
      obtain ⟨u, hu⟩ := hs ⟨0, by omega⟩
      obtain ⟨v, hv⟩ := hs ⟨m - 1, by omega⟩
      have he := hroot u.1.1 u.1.2 v.1.1 v.1.2
        (by left; exact congrArg Fin.val hu)
        (by right; left; have := congrArg Fin.val hv; dsimp [f] at this; omega)
        (induced_reachable_forced (C.reachable_of_mem_supp u.2 v.2))
      have := congrArg (fun x : GridVertex m m => x.1.val) he
      have hu' := congrArg Fin.val hu
      have hv' := congrArg Fin.val hv
      dsimp [f] at hu' hv'
      omega
    have := Fintype.card_lt_of_injective_not_surjective f hi hn
    simp only [Fintype.card_fin] at this
    omega

/-- Occupancy of a physical row interval gives a forced path along that row. -/
theorem row_interval_reachable {m : Nat} {F : Set (GridVertex m m)}
    (r a b : Fin m) (hab : a.val ≤ b.val)
    (hF : ∀ j : Fin m, a.val ≤ j.val → j.val ≤ b.val → (r, j) ∈ F) :
    (forcedEdgeGraph (gridGraph m m) F).Reachable (r, a) (r, b) := by
  have go : ∀ d : Nat, ∀ hd : a.val + d < m,
      a.val + d ≤ b.val →
      (forcedEdgeGraph (gridGraph m m) F).Reachable (r, a) (r, ⟨a.val + d, hd⟩) := by
    intro d
    induction d with
    | zero => intro hd _; exact .rfl
    | succ d ih =>
      intro hd hdb
      have hp := ih (by omega) (by omega)
      have he : (forcedEdgeGraph (gridGraph m m) F).Adj
          (r, ⟨a.val + d, by omega⟩) (r, ⟨a.val + (d + 1), hd⟩) := by
        refine ⟨?_, Or.inl (hF _ (by simp) (by simp; omega))⟩
        simp [gridGraph, adjacent]
        omega
      exact hp.trans he.reachable
  simpa [Nat.add_sub_of_le hab] using go (b.val - a.val) (by omega) (by omega)

/-- Two occupied rays with different boundary roots need two intervening U
vertices. The assertion uses actual occupancy and forced reachability. -/
theorem reciprocal_ray_cap {m : Nat} (hm : 2 ≤ m)
    {F : Set (GridVertex m m)} (hroot : UniqueBoundaryRoots F)
    (r a b : Fin m)
    (hleft : ∀ j : Fin m, j.val ≤ a.val → (r, j) ∈ F)
    (hright : ∀ j : Fin m, b.val ≤ j.val → (r, j) ∈ F) :
    (a.val + 1) + (m - b.val) ≤ m - 2 := by
  let l : Fin m := ⟨0, by omega⟩
  let t : Fin m := ⟨m - 1, by omega⟩
  have hnot : ¬ (forcedEdgeGraph (gridGraph m m) F).Reachable (r, l) (r, t) := by
    intro h
    have he := hroot (r, l) (hleft _ (by simp [l])) (r, t)
      (hright _ (by dsimp [t]; omega))
      (by simp [l, IsGridBoundary]) (by simp [t, IsGridBoundary]; omega) h
    have := congrArg (fun x : GridVertex m m => x.2.val) he
    dsimp [l, t] at this
    omega
  have hR := row_interval_reachable r b t (by dsimp [t]; omega)
    (fun j hj _ => hright j hj)
  have hsep : a.val + 2 < b.val := by
    by_contra hn
    by_cases hba : b.val ≤ a.val
    · exact hnot ((row_interval_reachable r l b (by simp [l])
        (fun j _ hj => hleft j (by omega))).trans hR)
    have hL := row_interval_reachable r l a (by simp [l]) (fun j _ hj => hleft j hj)
    by_cases hab : a.val + 1 = b.val
    · have he : (forcedEdgeGraph (gridGraph m m) F).Adj (r, a) (r, b) :=
        ⟨by simp [gridGraph, adjacent, hab], Or.inl (hleft a le_rfl)⟩
      exact hnot (hL.trans (he.reachable.trans hR))
    · let s : Fin m := ⟨a.val + 1, by omega⟩
      have he : (forcedEdgeGraph (gridGraph m m) F).Adj (r, a) (r, s) :=
        ⟨by simp [gridGraph, adjacent, s], Or.inl (hleft a le_rfl)⟩
      have he' : (forcedEdgeGraph (gridGraph m m) F).Adj (r, s) (r, b) := by
        refine ⟨?_, Or.inr (hright b le_rfl)⟩
        simp [gridGraph, adjacent, s]
        omega
      exact hnot (hL.trans (he.reachable.trans (he'.reachable.trans hR)))
  omega

/-- A left root next to the top-left corner cannot reach column m-3 if the
top-right corner is covered. This is the m-3 length cap, not an assumed loss. -/
theorem covered_destination_ray_cap {m : Nat} (hm : 4 ≤ m)
    {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (hroot : UniqueBoundaryRoots F) (a : Fin m)
    (hleft : ∀ j : Fin m, j.val ≤ a.val → (⟨1, by omega⟩, j) ∈ F)
    (hcover : (⟨0, by omega⟩, ⟨m - 2, by omega⟩) ∈ F ∨
      (⟨1, by omega⟩, ⟨m - 1, by omega⟩) ∈ F) :
    a.val + 1 ≤ m - 3 := by
  by_contra hn
  have hp : (⟨1, by omega⟩, ⟨m - 3, by omega⟩) ∈ F := hleft _ (by simp; omega)
  rcases hcover with htop | hright
  · have hcell := grid_cell_has_unforced_edge
      (m := m) (n := m) ⟨0, by omega⟩ ⟨m - 3, by omega⟩ hacyc
    have he : m - 3 + 1 = m - 2 := by omega
    simp only [cell00, cell01, cell11, cell10, he] at hcell
    rcases hcell with h | h | h | h
    · exact h.2 htop
    · exact h.1 htop
    · exact h.2 hp
    · exact h.1 hp
  · have h := reciprocal_ray_cap (by omega) hroot ⟨1, by omega⟩ a
      ⟨m - 1, by omega⟩ hleft (by
        intro j hj
        have he : j = (⟨m - 1, by omega⟩ : Fin m) := by
          apply Fin.ext
          change j.val = m - 1
          change m - 1 ≤ j.val at hj
          omega
        simpa [he] using hright)
    omega

/-- A carrier rooted on the left boundary is horizontal, including the
singleton case: a vertical extension would immediately give a second root. -/
theorem left_root_horizontal {m : Nat} {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (hroot : UniqueBoundaryRoots F)
    (C : ((gridGraph m m).induce F).ConnectedComponent)
    (u : F) (hu : u ∈ C.supp) (hu0 : u.1.2.val = 0) :
    ∀ v ∈ C.supp, v.1.1 = u.1.1 := by
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · intro v hv
    exact (hr v hv).trans (hr u hu).symm
  · intro v hv
    have hv0 : v.1.2.val = 0 := by rw [(hc v hv).trans (hc u hu).symm]; exact hu0
    have he := hroot u.1 u.2 v.1 v.2
      (by right; right; left; exact hu0) (by right; right; left; exact hv0)
      (induced_reachable_forced (C.reachable_of_mem_supp hu hv))
    exact (congrArg Prod.fst he).symm

/-- Extract the physical interval of a left-rooted induced component.
The size is counted by a bijection, not supplied as a numerical hypothesis. -/
theorem left_root_interval {m : Nat} {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (hroot : UniqueBoundaryRoots F)
    (C : ((gridGraph m m).induce F).ConnectedComponent)
    (u : F) (hu : u ∈ C.supp) (hu0 : u.1.2.val = 0) :
    ∃ a : Fin m, C.supp.ncard = a.val + 1 ∧
      ∀ j : Fin m, j.val ≤ a.val → (u.1.1, j) ∈ F := by
  classical
  have hrow := left_root_horizontal hacyc hroot C u hu hu0
  let S : Finset (Fin m) := C.supp.toFinset.image (fun v => v.1.2)
  have hS : S.Nonempty := ⟨u.1.2, mem_image.mpr ⟨u, by simpa using hu, rfl⟩⟩
  let a := S.max' hS
  obtain ⟨v, hv, hva⟩ := mem_image.mp (max'_mem S hS)
  have hvC : v ∈ C.supp := by simpa using hv
  have hfill (j : Fin m) (hj : j.val ≤ a.val) :
      ∃ hjF : (u.1.1, j) ∈ F, (⟨(u.1.1, j), hjF⟩ : F) ∈ C.supp := by
    apply induced_forced_connectedComponent_horizontal_interval_of_le hacyc C hu hvC
      (hrow v hvC).symm j (by omega)
    rw [hva]
    exact hj
  refine ⟨a, ?_, fun j hj => (hfill j hj).1⟩
  rw [Set.ncard_eq_toFinset_card']
  have hi : Set.InjOn (fun v : F => v.1.2) C.supp.toFinset := by
    intro v hv w hw he
    exact Subtype.ext (Prod.ext ((hrow v (by simpa using hv)).trans
      (hrow w (by simpa using hw)).symm) he)
  have heq : S = Iic a := by
    ext j
    constructor
    · intro hj
      exact mem_Iic.mpr (le_max' S j hj)
    · intro hj
      obtain ⟨hjF, hjC⟩ := hfill j (show j ≤ a from mem_Iic.mp hj)
      exact mem_image.mpr ⟨⟨(u.1.1, j), hjF⟩, by simpa using hjC, rfl⟩
  rw [← card_image_of_injOn hi]
  change S.card = a.val + 1
  rw [heq]
  simp

/-- The strengthened cap now applies to an actual induced component rooted
at (1,0), without an assumed interval or an assumed carrier length. -/
theorem covered_destination_component_cap {m : Nat} (hm : 4 ≤ m)
    {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (hroot : UniqueBoundaryRoots F)
    (C : ((gridGraph m m).induce F).ConnectedComponent)
    (huF : (⟨1, by omega⟩, ⟨0, by omega⟩) ∈ F)
    (hu : (⟨(⟨1, by omega⟩, ⟨0, by omega⟩), huF⟩ : F) ∈ C.supp)
    (hcover : (⟨0, by omega⟩, ⟨m - 2, by omega⟩) ∈ F ∨
      (⟨1, by omega⟩, ⟨m - 1, by omega⟩) ∈ F) :
    C.supp.ncard ≤ m - 3 := by
  obtain ⟨a, ha, hfill⟩ := left_root_interval hacyc hroot C _ hu rfl
  rw [ha]
  exact covered_destination_ray_cap hm hacyc hroot a hfill hcover

/-- Right-boundary counterpart of the physical interval extraction. -/
theorem right_root_interval {m : Nat} {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (hroot : UniqueBoundaryRoots F)
    (C : ((gridGraph m m).induce F).ConnectedComponent)
    (u : F) (hu : u ∈ C.supp) (hu0 : u.1.2.val + 1 = m) :
    ∃ b : Fin m, C.supp.ncard = m - b.val ∧
      ∀ j : Fin m, b.val ≤ j.val → (u.1.1, j) ∈ F := by
  classical
  have hrow : ∀ v ∈ C.supp, v.1.1 = u.1.1 := by
    rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
    · intro v hv
      exact (hr v hv).trans (hr u hu).symm
    · intro v hv
      have hv0 : v.1.2.val + 1 = m := by rw [(hc v hv).trans (hc u hu).symm]; exact hu0
      have he := hroot u.1 u.2 v.1 v.2
        (by right; right; right; exact hu0) (by right; right; right; exact hv0)
        (induced_reachable_forced (C.reachable_of_mem_supp hu hv))
      exact (congrArg Prod.fst he).symm
  let S : Finset (Fin m) := C.supp.toFinset.image (fun v => v.1.2)
  have hS : S.Nonempty := ⟨u.1.2, mem_image.mpr ⟨u, by simpa using hu, rfl⟩⟩
  let b := S.min' hS
  obtain ⟨v, hv, hvb⟩ := mem_image.mp (min'_mem S hS)
  have hvC : v ∈ C.supp := by simpa using hv
  have hfill (j : Fin m) (hj : b.val ≤ j.val) :
      ∃ hjF : (u.1.1, j) ∈ F, (⟨(u.1.1, j), hjF⟩ : F) ∈ C.supp := by
    have h := induced_forced_connectedComponent_horizontal_interval_of_le hacyc C hvC hu
      (hrow v hvC) j (by rw [hvb]; exact hj) (by omega)
    simpa only [hrow v hvC] using h
  refine ⟨b, ?_, fun j hj => (hfill j hj).1⟩
  rw [Set.ncard_eq_toFinset_card']
  have hi : Set.InjOn (fun v : F => v.1.2) C.supp.toFinset := by
    intro v hv w hw he
    exact Subtype.ext (Prod.ext ((hrow v (by simpa using hv)).trans
      (hrow w (by simpa using hw)).symm) he)
  have heq : S = Ici b := by
    ext j
    constructor
    · intro hj
      exact mem_Ici.mpr (min'_le S j hj)
    · intro hj
      obtain ⟨hjF, hjC⟩ := hfill j (show b ≤ j from mem_Ici.mp hj)
      exact mem_image.mpr ⟨⟨(u.1.1, j), hjF⟩, by simpa using hjC, rfl⟩
  rw [← card_image_of_injOn hi]
  change S.card = m - b.val
  rw [heq]
  simp

/-- Actual reciprocal induced components, with neither lengths nor
separation supplied as hypotheses. The row can be any row of the square. -/
theorem reciprocal_component_cap {m : Nat} (hm : 2 ≤ m)
    {F : Set (GridVertex m m)}
    (hacyc : (forcedEdgeGraph (gridGraph m m) F).IsAcyclic)
    (hroot : UniqueBoundaryRoots F)
    (C D : ((gridGraph m m).induce F).ConnectedComponent)
    (u v : F) (hu : u ∈ C.supp) (hv : v ∈ D.supp)
    (hu0 : u.1.2.val = 0) (hvm : v.1.2.val + 1 = m)
    (hrow : u.1.1 = v.1.1) :
    C ≠ D ∧ C.supp.ncard + D.supp.ncard ≤ m - 2 := by
  have hne : C ≠ D := by
    intro he
    have hv' : v ∈ C.supp := by rw [he]; exact hv
    have he := hroot u.1 u.2 v.1 v.2
      (by right; right; left; exact hu0) (by right; right; right; exact hvm)
      (induced_reachable_forced (C.reachable_of_mem_supp hu hv'))
    have := congrArg (fun x : GridVertex m m => x.2.val) he
    omega
  obtain ⟨a, ha, hleft⟩ := left_root_interval hacyc hroot C u hu hu0
  obtain ⟨b, hb, hright⟩ := right_root_interval hacyc hroot D v hv hvm
  refine ⟨hne, ?_⟩
  rw [ha, hb]
  exact reciprocal_ray_cap hm hroot u.1.1 a b hleft (by simpa only [hrow] using hright)

end GridGraphs.BoundaryFive.Rootless
