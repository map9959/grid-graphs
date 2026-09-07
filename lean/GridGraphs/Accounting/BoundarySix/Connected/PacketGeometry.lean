import GridGraphs.Accounting.BoundarySix.Connected.PacketCount

/-! # Literal paths in the two corner patches -/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

def cornerReflect {n : Nat} (l : Bool × Bool) (v : GridVertex n n) : GridVertex n n :=
  (if l.1 then v.1 else v.1.rev, if l.2 then v.2 else v.2.rev)

theorem cornerReflect_involutive {n : Nat} (l : Bool × Bool) :
    Function.Involutive (cornerReflect (n := n) l) := by
  intro v
  rcases l with ⟨a, b⟩
  cases a <;> cases b <;> simp [cornerReflect]

theorem cornerReflect_adj {n : Nat} (l : Bool × Bool) (v w : GridVertex n n) :
    (gridGraph n n).Adj (cornerReflect l v) (cornerReflect l w) ↔ (gridGraph n n).Adj v w := by
  rcases l with ⟨a, b⟩
  cases a <;> cases b <;> simp [cornerReflect, gridGraph, adjacent, Fin.ext_iff] <;> omega

theorem cornerReflect_boundary {n : Nat} (l : Bool × Bool) (v : GridVertex n n) :
    IsGridBoundary (cornerReflect l v) ↔ IsGridBoundary v := by
  rcases l with ⟨a, b⟩
  cases a <;> cases b <;> simp [cornerReflect, IsGridBoundary] <;> omega

theorem cornerReflect_near {n : Nat} (l : Bool × Bool) (v : GridVertex n n) :
    Near (cornerReflect l v) ↔ Near v := by
  rcases l with ⟨a, b⟩
  cases a <;> cases b <;> simp [cornerReflect, Near] <;> omega

theorem cornerReflect_second {n : Nat} (l : Bool × Bool) (v : GridVertex n n) :
    Second (cornerReflect l v) ↔ Second v := by
  rcases l with ⟨a, b⟩
  cases a <;> cases b <;> simp [cornerReflect, Second] <;> omega

theorem cornerReflect_ring {n : Nat} (hn : 3 ≤ n) (l : Bool × Bool) (v : GridVertex n n) :
    IsNextRing (cornerReflect l v) ↔ IsNextRing v := by
  rcases l with ⟨a, b⟩
  cases a <;> cases b <;> simp [cornerReflect, IsNextRing] <;> omega

theorem cornerReflect_small_label {n : Nat} (hn : 9 ≤ n) (l : Bool × Bool)
    (v : GridVertex n n) (hr : v.1.val ≤ 2) (hc : v.2.val ≤ 2) :
    cornerLabel (cornerReflect l v) = l := by
  rcases l with ⟨a, b⟩
  cases a <;> cases b <;> simp [cornerReflect, cornerLabel] <;> omega

theorem cornerReflect_patch_label {n : Nat} (hn : 9 ≤ n) (l : Bool × Bool)
    (v : GridVertex n n) (hr : v.1.val ≤ 3) (hc : v.2.val ≤ 3) :
    patchLabel (cornerReflect l v) = l := by
  rcases l with ⟨a, b⟩
  cases a <;> cases b <;> simp [cornerReflect, patchLabel] <;> omega

theorem second_reflect_shape {n : Nat} (hn : 9 ≤ n) {u : GridVertex n n} (hu : Second u) :
    u = cornerReflect (cornerLabel u) (⟨0, by omega⟩, ⟨2, by omega⟩) ∨
      u = cornerReflect (cornerLabel u) (⟨2, by omega⟩, ⟨0, by omega⟩) := by
  unfold Second at hu
  by_cases hr : u.1.val < 3 <;> by_cases hc : u.2.val < 3 <;>
    simp [cornerReflect, cornerLabel, hr, hc, Prod.ext_iff, Fin.ext_iff] <;> omega

theorem deepCorner_reflect {n : Nat} (hn : 9 ≤ n) {z : GridVertex n n} (hz : IsDeepCorner z) :
    z = cornerReflect (cornerLabel z) (⟨2, by omega⟩, ⟨2, by omega⟩) := by
  unfold IsDeepCorner at hz
  by_cases hr : z.1.val < 3 <;> by_cases hc : z.2.val < 3 <;>
    simp [cornerReflect, cornerLabel, hr, hc, Prod.ext_iff, Fin.ext_iff] <;> omega

private def localPoint {n : Nat} (hn : 9 ≤ n) (left down : Bool) : Fin 6 → GridVertex n n :=
  ![if left then (⟨2, by omega⟩, ⟨0, by omega⟩) else (⟨0, by omega⟩, ⟨2, by omega⟩),
    if left then (⟨2, by omega⟩, ⟨1, by omega⟩) else (⟨1, by omega⟩, ⟨2, by omega⟩),
    (⟨2, by omega⟩, ⟨2, by omega⟩),
    if down then (⟨3, by omega⟩, ⟨2, by omega⟩) else (⟨2, by omega⟩, ⟨3, by omega⟩),
    if down then (⟨3, by omega⟩, ⟨1, by omega⟩) else (⟨1, by omega⟩, ⟨3, by omega⟩),
    if down then (⟨3, by omega⟩, ⟨0, by omega⟩) else (⟨0, by omega⟩, ⟨3, by omega⟩)]

private theorem localPoint_injective {n : Nat} (hn : 9 ≤ n) (left down : Bool) :
    Function.Injective (localPoint hn left down) := by
  intro i j he
  cases left <;> cases down <;> fin_cases i <;> fin_cases j <;>
    simp_all [localPoint, Prod.ext_iff, Fin.ext_iff]

private theorem localPoint_adj {n : Nat} (hn : 9 ≤ n) (left down : Bool) (i : Fin 5) :
    (gridGraph n n).Adj (localPoint hn left down i.castSucc) (localPoint hn left down i.succ) := by
  cases left <;> cases down <;> fin_cases i <;> simp [localPoint, gridGraph, adjacent]

private theorem localPoint_boundary {n : Nat} (hn : 9 ≤ n) (left down : Bool) (i : Fin 6) :
    IsGridBoundary (localPoint hn left down i) ↔ i = 0 ∨ i = 5 := by
  cases left <;> cases down <;> fin_cases i <;> simp [localPoint, IsGridBoundary, Fin.ext_iff] <;> omega

/-- A preserved neighbor of the deep corner supplies a literal five-edge
packet. The two extra boundary holes have different corner labels. -/
theorem corner_packet_of_neighbor {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n)) (hEmpty : F.filter IsNextRing = ∅)
    (u v : GridVertex n n) (hu : Second u) (hv : Second v)
    (huv : cornerLabel u ≠ cornerLabel v)
    (hcover : ∀ x, x ∉ F → IsGridBoundary x → Near x ∨ x = u ∨ x = v)
    (hzF : cornerReflect (cornerLabel u) (⟨2, by omega⟩, ⟨2, by omega⟩) ∈ F)
    (hneighbor : ∃ w ∈ F, (gridGraph n n).Adj
      (cornerReflect (cornerLabel u) (⟨2, by omega⟩, ⟨2, by omega⟩)) w) :
    Nonempty (CornerPacket (forcedEdgeGraph (gridGraph n n) (↑F : Set _)) (cornerLabel u)) := by
  let l := cornerLabel u
  have forced (x : GridVertex n n) (hxb : IsGridBoundary x)
      (hxn : ¬ Near x) (hxu : x ≠ u) (hxv : x ≠ v) : x ∈ F := by
    by_contra hx
    exact (hcover x hx hxb).elim hxn (fun h => h.elim hxu hxv)
  obtain ⟨w, hwF, hwAdj⟩ := hneighbor
  let a := cornerReflect l w
  have haF : cornerReflect l a ∈ F := by
    dsimp only [a]
    rw [cornerReflect_involutive l w]
    exact hwF
  have haAdj : (gridGraph n n).Adj (⟨2, by omega⟩, ⟨2, by omega⟩) a := by
    apply (cornerReflect_adj l _ _).mp
    dsimp only [a]
    rw [cornerReflect_involutive l w]
    exact hwAdj
  have haRing : ¬ IsNextRing a := by
    intro ha
    have hm := mem_filter.mpr ⟨haF, (cornerReflect_ring (by omega) l a).mpr ha⟩
    rw [hEmpty] at hm
    exact notMem_empty _ hm
  have ha : a = (⟨3, by omega⟩, ⟨2, by omega⟩) ∨ a = (⟨2, by omega⟩, ⟨3, by omega⟩) := by
    simp only [gridGraph, adjacent, Fin.ext_iff] at haAdj
    simp only [Prod.ext_iff, Fin.ext_iff]
    unfold IsNextRing at haRing
    omega
  obtain ⟨down, hdown⟩ : ∃ down : Bool, cornerReflect l
      (if down then (⟨3, by omega⟩, ⟨2, by omega⟩) else (⟨2, by omega⟩, ⟨3, by omega⟩)) ∈ F := by
    rcases ha with ha | ha
    · exact ⟨true, by simpa only [ha, Bool.true_eq, if_true] using haF⟩
    · exact ⟨false, by simpa only [ha, Bool.false_eq_true, if_false] using haF⟩
  obtain ⟨left, hleft⟩ : ∃ left : Bool, u = cornerReflect l
      (if left then (⟨0, by omega⟩, ⟨2, by omega⟩) else (⟨2, by omega⟩, ⟨0, by omega⟩)) := by
    rcases second_reflect_shape hn hu with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  let p := fun i => cornerReflect l (localPoint hn left down i)
  have h0 : p 0 ∈ F := by
    apply forced
    · rw [cornerReflect_boundary]
      cases left <;> simp [localPoint, IsGridBoundary]
    · rw [cornerReflect_near]
      cases left <;> simp [localPoint, Near] <;> omega
    · intro he
      rw [hleft] at he
      have h := (cornerReflect_involutive l).injective he
      cases left <;> simp [localPoint] at h
    · intro he
      have hl : cornerLabel (p 0) = l := by
        apply cornerReflect_small_label hn
        · cases left <;> simp [localPoint]
        · cases left <;> simp [localPoint]
      exact huv (hl.symm.trans (congrArg cornerLabel he))
  have h5 : p 5 ∈ F := by
    have hb5 : IsGridBoundary (p 5) := by
      rw [cornerReflect_boundary]
      cases down <;> simp [localPoint, IsGridBoundary]
    have hn5 : ¬ Near (p 5) := by
      rw [cornerReflect_near]
      cases down <;> simp [localPoint, Near] <;> omega
    have hs5 : ¬ Second (p 5) := by
      rw [cornerReflect_second]
      cases down <;> simp [localPoint, Second] <;> omega
    exact forced _ hb5 hn5 (fun he => hs5 (he ▸ hu)) (fun he => hs5 (he ▸ hv))
  have h2 : p 2 ∈ F := hzF
  have h3 : p 3 ∈ F := hdown
  refine ⟨⟨p, (cornerReflect_involutive l).injective.comp (localPoint_injective hn left down),
    ?_, ?_, ?_⟩⟩
  · intro i
    refine ⟨(cornerReflect_adj l _ _).mpr (localPoint_adj hn left down i), ?_⟩
    fin_cases i
    · exact Or.inl h0
    · exact Or.inr h2
    · exact Or.inl h2
    · exact Or.inl h3
    · exact Or.inr h5
  · intro i
    exact (cornerReflect_boundary l _).trans (localPoint_boundary hn left down i)
  · intro i
    apply cornerReflect_patch_label hn
    · cases left <;> cases down <;> fin_cases i <;> simp [localPoint]
    · cases left <;> cases down <;> fin_cases i <;> simp [localPoint]

end GridGraphs.BoundarySix.Connected
