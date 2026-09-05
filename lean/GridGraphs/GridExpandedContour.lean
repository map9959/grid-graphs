import GridGraphs.TreeContour
import GridGraphs.GridOuterPortContour

/-!
# Expanded grid contour

The expanded contour uses every compass slot at every grid vertex.  Occupied
slots cross a retained edge and turn clockwise from its reverse direction;
unoccupied slots turn clockwise in place.  Its first return to occupied slots
is the directional-dart contour permutation.
-/

namespace GridGraphs

namespace GridDirection

/-- One counterclockwise quarter-turn. -/
def counterclockwise : GridDirection → GridDirection
  | .north => .west
  | .east => .north
  | .south => .east
  | .west => .south

@[simp] theorem counterclockwise_clockwise (d : GridDirection) :
    d.counterclockwise.clockwise = d := by cases d <;> rfl

@[simp] theorem clockwise_counterclockwise (d : GridDirection) :
    d.clockwise.counterclockwise = d := by cases d <;> rfl

end GridDirection

/-- A compass slot based at a grid vertex. -/
abbrev GridCompassSlot (m n : Nat) := GridVertex m n × GridDirection

namespace GridExpandedContour

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- A slot is occupied when its direction is a retained edge direction. -/
def Occupied (s : GridCompassSlot m n) : Prop :=
  s.2 ∈ GridDirectionalDart.directionsAt (T := T) s.1

/-- Expanded successor: cross and turn after a retained direction, and only
turn at a missing direction. -/
noncomputable def succ (s : GridCompassSlot m n) : GridCompassSlot m n :=
  if h : s.2 ∈ GridDirectionalDart.directionsAt (T := T) s.1 then
    let d := GridDirectionalDart.ofDirectionMem (T := T) s.1 s.2 h
    (d.target, s.2.opposite.clockwise)
  else
    (s.1, s.2.clockwise)

/-- Explicit inverse expanded move, inspecting the counterclockwise slot. -/
noncomputable def pred (s : GridCompassSlot m n) : GridCompassSlot m n :=
  let e := s.2.counterclockwise
  if h : e ∈ GridDirectionalDart.directionsAt (T := T) s.1 then
    let d := GridDirectionalDart.ofDirectionMem (T := T) s.1 e h
    (d.target, e.opposite)
  else
    (s.1, e)

theorem succ_of_occupied {s : GridCompassSlot m n}
    (h : Occupied (T := T) s) :
    succ (T := T) s =
      ((GridDirectionalDart.ofDirectionMem (T := T) s.1 s.2 h).target,
        s.2.opposite.clockwise) := by
  change s.2 ∈ GridDirectionalDart.directionsAt (T := T) s.1 at h
  simp [succ, h]

theorem succ_of_not_occupied {s : GridCompassSlot m n}
    (h : ¬Occupied (T := T) s) :
    succ (T := T) s = (s.1, s.2.clockwise) := by
  change s.2 ∉ GridDirectionalDart.directionsAt (T := T) s.1 at h
  simp [succ, h]

theorem ofDirectionMem_reverse_target (d : GridDirectionalDart T) :
    (GridDirectionalDart.ofDirectionMem (T := T) d.target
      d.direction.opposite (GridDirectionalDart.reverse_direction_mem d)).target =
        d.source := by
  have heq : GridDirectionalDart.ofDirectionMem (T := T) d.target
      d.direction.opposite (GridDirectionalDart.reverse_direction_mem d) = d.reverse :=
    GridDirectionalDart.ext rfl rfl
  simpa [GridDirectionalDart.reverse] using
    congrArg GridDirectionalDart.target heq

@[simp] theorem succ_pred (s : GridCompassSlot m n) :
    succ (T := T) (pred (T := T) s) = s := by
  rcases s with ⟨v, e⟩
  by_cases h : e.counterclockwise ∈
      GridDirectionalDart.directionsAt (T := T) v
  · let d := GridDirectionalDart.ofDirectionMem (T := T) v e.counterclockwise h
    have hreverse : Occupied (T := T) (d.target, e.counterclockwise.opposite) := by
      change e.counterclockwise.opposite ∈
        GridDirectionalDart.directionsAt (T := T) d.target
      simpa [d] using GridDirectionalDart.reverse_direction_mem d
    rw [show pred (T := T) (v, e) = (d.target, e.counterclockwise.opposite) by
      simp [pred, h, d]]
    rw [succ_of_occupied hreverse]
    have htarget :
        (GridDirectionalDart.ofDirectionMem (T := T) d.target
          e.counterclockwise.opposite hreverse).target = v := by
      have heq : GridDirectionalDart.ofDirectionMem (T := T) d.target
          e.counterclockwise.opposite hreverse = d.reverse :=
        GridDirectionalDart.ext rfl (by rfl)
      simpa [GridDirectionalDart.reverse, d] using
        congrArg GridDirectionalDart.target heq
    rw [htarget]
    fin_cases e <;> rfl
  · rw [show pred (T := T) (v, e) = (v, e.counterclockwise) by simp [pred, h]]
    rw [succ_of_not_occupied (T := T) (by simpa [Occupied] using h)]
    simp

@[simp] theorem pred_succ (s : GridCompassSlot m n) :
    pred (T := T) (succ (T := T) s) = s := by
  rcases s with ⟨v, e⟩
  by_cases h : Occupied (T := T) (v, e)
  · let d := GridDirectionalDart.ofDirectionMem (T := T) v e h
    rw [succ_of_occupied h]
    have hreverse : e.opposite ∈
        GridDirectionalDart.directionsAt (T := T) d.target := by
      simpa [d] using GridDirectionalDart.reverse_direction_mem d
    rw [show pred (T := T) (d.target, e.opposite.clockwise) =
        ((GridDirectionalDart.ofDirectionMem (T := T) d.target
          e.opposite hreverse).target, e) by
      simp [pred, hreverse]]
    have htarget :
        (GridDirectionalDart.ofDirectionMem (T := T) d.target e.opposite hreverse).target = v := by
      have heq : GridDirectionalDart.ofDirectionMem (T := T) d.target
          e.opposite hreverse = d.reverse := GridDirectionalDart.ext rfl (by rfl)
      simpa [GridDirectionalDart.reverse, d] using
        congrArg GridDirectionalDart.target heq
    rw [htarget]
  · rw [succ_of_not_occupied h]
    change e ∉ GridDirectionalDart.directionsAt (T := T) v at h
    simp [pred, h]

/-- Expanded contour as a permutation of all compass slots. -/
noncomputable def equiv : GridCompassSlot m n ≃ GridCompassSlot m n where
  toFun := succ (T := T)
  invFun := pred (T := T)
  left_inv := pred_succ
  right_inv := succ_pred

@[simp] theorem equiv_apply (s : GridCompassSlot m n) :
    equiv (T := T) s = succ (T := T) s := rfl

/-- The occupied slot represented by a directional dart. -/
def slotOfDart (d : GridDirectionalDart T) : GridCompassSlot m n :=
  (d.source, d.direction)

theorem occupied_slotOfDart (d : GridDirectionalDart T) :
    Occupied (T := T) (slotOfDart d) := by
  rw [Occupied, GridDirectionalDart.mem_directionsAt]
  exact ⟨d.target, d.step, d.adj⟩

omit [DecidableRel T.Adj] in theorem slotOfDart_injective :
    Function.Injective (@slotOfDart m n T) := by
  intro a b h
  exact GridDirectionalDart.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

@[simp] theorem succ_slotOfDart (d : GridDirectionalDart T) :
    succ (T := T) (slotOfDart d) =
      (d.target, d.direction.opposite.clockwise) := by
  rw [succ_of_occupied (occupied_slotOfDart d)]
  congr 1
  exact congrArg GridDirectionalDart.target (GridDirectionalDart.ext rfl rfl)

/-- Expanded contour slots based at vertices in a dart's target shore. -/
noncomputable def expandedTargetShoreSlots (d : GridDirectionalDart T) :
    Finset (GridCompassSlot m n) :=
  Finset.univ.filter fun slot => slot.1 ∈ d.targetShoreVertices

@[simp] theorem mem_expandedTargetShoreSlots
    (d : GridDirectionalDart T) (slot : GridCompassSlot m n) :
    slot ∈ expandedTargetShoreSlots d ↔ slot.1 ∈ d.targetShoreVertices := by
  simp [expandedTargetShoreSlots]

theorem succ_mem_expandedTargetShoreSlots_iff_of_notMem
    (hacyclic : T.IsAcyclic) (d : GridDirectionalDart T)
    (slot : GridCompassSlot m n)
    (hout : slot ∉ expandedTargetShoreSlots d) :
    succ (T := T) slot ∈ expandedTargetShoreSlots d ↔
      slot = slotOfDart d := by
  by_cases hoccupied : Occupied (T := T) slot
  · let x := GridDirectionalDart.ofDirectionMem (T := T) slot.1 slot.2 hoccupied
    have hsucc : succ (T := T) slot =
        (x.target, slot.2.opposite.clockwise) := succ_of_occupied hoccupied
    constructor
    · intro hin
      have hxOut : x.source ∉ d.targetShoreVertices := by
        simpa [mem_expandedTargetShoreSlots, x] using hout
      have hxIn : x.target ∈ d.targetShoreVertices := by
        simpa [mem_expandedTargetShoreSlots, hsucc] using hin
      have hedge := GridDirectionalDart.edgeSym2_eq_of_source_mem_target_notMem
        d x.reverse (by simpa [GridDirectionalDart.reverse] using hxIn)
          (by simpa [GridDirectionalDart.reverse] using hxOut)
      rw [GridDirectionalDart.edgeSym2, GridDirectionalDart.edgeSym2,
        GridDirectionalDart.reverse, Sym2.eq_iff] at hedge
      rcases hedge with ⟨hxt, hxs⟩ | ⟨hxs, hxt⟩
      · have : d.source ∈ d.targetShoreVertices := hxt ▸ hxIn
        exact (GridDirectionalDart.source_notMem_targetShoreVertices
          hacyclic d this).elim
      · have hx : x = d := GridDirectionalDart.ext_endpoints hxt hxs
        simpa [slotOfDart, x] using congrArg slotOfDart hx
    · rintro rfl
      rw [mem_expandedTargetShoreSlots, succ_slotOfDart]
      exact d.target_mem_targetShoreVertices
  · rw [succ_of_not_occupied hoccupied]
    constructor
    · intro hin
      exact (hout (by simpa using hin)).elim
    · intro heq
      subst slot
      exact (hoccupied (occupied_slotOfDart d)).elim

theorem succ_notMem_expandedTargetShoreSlots_iff_of_mem
    (hacyclic : T.IsAcyclic) (d : GridDirectionalDart T)
    (slot : GridCompassSlot m n)
    (hin : slot ∈ expandedTargetShoreSlots d) :
    succ (T := T) slot ∉ expandedTargetShoreSlots d ↔
      slot = slotOfDart d.reverse := by
  by_cases hoccupied : Occupied (T := T) slot
  · let x := GridDirectionalDart.ofDirectionMem (T := T) slot.1 slot.2 hoccupied
    have hsucc : succ (T := T) slot =
        (x.target, slot.2.opposite.clockwise) := succ_of_occupied hoccupied
    constructor
    · intro hout
      have hxIn : x.source ∈ d.targetShoreVertices := by
        simpa [mem_expandedTargetShoreSlots, x] using hin
      have hxOut : x.target ∉ d.targetShoreVertices := by
        simpa [mem_expandedTargetShoreSlots, hsucc] using hout
      have hedge := GridDirectionalDart.edgeSym2_eq_of_source_mem_target_notMem
        d x hxIn hxOut
      rw [GridDirectionalDart.edgeSym2, GridDirectionalDart.edgeSym2,
        Sym2.eq_iff] at hedge
      rcases hedge with ⟨hxs, hxt⟩ | ⟨hxt, hxs⟩
      · have : d.source ∈ d.targetShoreVertices := hxs ▸ hxIn
        exact (GridDirectionalDart.source_notMem_targetShoreVertices
          hacyclic d this).elim
      · have hx : x = d.reverse := by
          apply GridDirectionalDart.ext_endpoints
          · simpa [GridDirectionalDart.reverse] using hxt
          · simpa [GridDirectionalDart.reverse] using hxs
        simpa [slotOfDart, x] using congrArg slotOfDart hx
    · rintro rfl
      rw [mem_expandedTargetShoreSlots, succ_slotOfDart]
      simpa [GridDirectionalDart.reverse] using
        GridDirectionalDart.source_notMem_targetShoreVertices hacyclic d
  · rw [succ_of_not_occupied hoccupied]
    constructor
    · intro hout
      exact (hout (by simpa using hin)).elim
    · intro heq
      subst slot
      exact (hoccupied (occupied_slotOfDart d.reverse)).elim

/-- Starting at an occupied dart slot, the first occupied expanded successor
is the ordinary contour successor, after one to four expanded moves. -/
theorem firstReturn_slotOfDart (d : GridDirectionalDart T) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 4 ∧
      (equiv (T := T)^[k]) (slotOfDart d) = slotOfDart d.contourSucc ∧
      ∀ j : Nat, 0 < j → j < k →
        ¬Occupied (T := T) ((equiv (T := T)^[j]) (slotOfDart d)) := by
  let S := GridDirectionalDart.directionsAt (T := T) d.target
  let incoming := d.direction.opposite
  let s₁ : GridCompassSlot m n := (d.target, incoming.clockwise)
  let s₂ : GridCompassSlot m n := (d.target, incoming.clockwise.clockwise)
  let s₃ : GridCompassSlot m n :=
    (d.target, incoming.clockwise.clockwise.clockwise)
  let s₄ : GridCompassSlot m n := (d.target, incoming)
  have hstart : equiv (T := T) (slotOfDart d) = s₁ := by
    simp [s₁, incoming]
  by_cases h₁ : incoming.clockwise ∈ S
  · refine ⟨1, by omega, by omega, ?_, ?_⟩
    · change equiv (T := T) (slotOfDart d) = slotOfDart d.contourSucc
      rw [hstart]
      simp [s₁, slotOfDart, GridDirectionalDart.contourSucc,
        GridDirection.nextIn, S, incoming, h₁]
    · intro j hj hjk
      omega
  · by_cases h₂ : incoming.clockwise.clockwise ∈ S
    · have hn₁ : ¬Occupied (T := T) s₁ := by
        simpa [Occupied, s₁, S] using h₁
      have hstep₂ : equiv (T := T) s₁ = s₂ := by
        rw [equiv_apply, succ_of_not_occupied hn₁]
      refine ⟨2, by omega, by omega, ?_, ?_⟩
      · change equiv (T := T) (equiv (T := T) (slotOfDart d)) =
          slotOfDart d.contourSucc
        rw [hstart, hstep₂]
        simp [s₂, slotOfDart, GridDirectionalDart.contourSucc,
          GridDirection.nextIn, S, incoming, h₁, h₂]
      · intro j hj hjk
        have : j = 1 := by omega
        subst j
        change ¬Occupied (T := T) (equiv (T := T) (slotOfDart d))
        simpa [hstart] using hn₁
    · by_cases h₃ : incoming.clockwise.clockwise.clockwise ∈ S
      · have hn₁ : ¬Occupied (T := T) s₁ := by
          simpa [Occupied, s₁, S] using h₁
        have hn₂ : ¬Occupied (T := T) s₂ := by
          simpa [Occupied, s₂, S] using h₂
        have hstep₂ : equiv (T := T) s₁ = s₂ := by
          rw [equiv_apply, succ_of_not_occupied hn₁]
        have hstep₃ : equiv (T := T) s₂ = s₃ := by
          rw [equiv_apply, succ_of_not_occupied hn₂]
        refine ⟨3, by omega, by omega, ?_, ?_⟩
        · change equiv (T := T)
            (equiv (T := T) (equiv (T := T) (slotOfDart d))) =
              slotOfDart d.contourSucc
          rw [hstart, hstep₂, hstep₃]
          simp [s₃, slotOfDart, GridDirectionalDart.contourSucc,
            GridDirection.nextIn, S, incoming, h₁, h₂, h₃]
        · intro j hj hjk
          interval_cases j
          · change ¬Occupied (T := T) (equiv (T := T) (slotOfDart d))
            simpa [hstart] using hn₁
          · change ¬Occupied (T := T)
              (equiv (T := T) (equiv (T := T) (slotOfDart d)))
            simpa [hstart, hstep₂] using hn₂
      · refine ⟨4, by omega, by omega, ?_, ?_⟩
        · have hn₁ : ¬Occupied (T := T) s₁ := by
            simpa [Occupied, s₁, S] using h₁
          have hn₂ : ¬Occupied (T := T) s₂ := by
            simpa [Occupied, s₂, S] using h₂
          have hn₃ : ¬Occupied (T := T) s₃ := by
            simpa [Occupied, s₃, S] using h₃
          have hstep₂ : equiv (T := T) s₁ = s₂ := by
            rw [equiv_apply, succ_of_not_occupied hn₁]
          have hstep₃ : equiv (T := T) s₂ = s₃ := by
            rw [equiv_apply, succ_of_not_occupied hn₂]
          have hstep₄ : equiv (T := T) s₃ = s₄ := by
            rw [equiv_apply, succ_of_not_occupied hn₃]
            simp [s₃, s₄, incoming]
          change equiv (T := T) (equiv (T := T)
            (equiv (T := T) (equiv (T := T) (slotOfDart d)))) =
              slotOfDart d.contourSucc
          rw [hstart, hstep₂, hstep₃, hstep₄]
          simp [s₄, slotOfDart, GridDirectionalDart.contourSucc,
            GridDirection.nextIn, S, incoming, h₁, h₂, h₃]
        · intro j hj hjk
          have hn₁ : ¬Occupied (T := T) s₁ := by
            simpa [Occupied, s₁, S] using h₁
          have hn₂ : ¬Occupied (T := T) s₂ := by
            simpa [Occupied, s₂, S] using h₂
          have hn₃ : ¬Occupied (T := T) s₃ := by
            simpa [Occupied, s₃, S] using h₃
          have hstep₂ : equiv (T := T) s₁ = s₂ := by
            rw [equiv_apply, succ_of_not_occupied hn₁]
          have hstep₃ : equiv (T := T) s₂ = s₃ := by
            rw [equiv_apply, succ_of_not_occupied hn₂]
          interval_cases j
          · change ¬Occupied (T := T) (equiv (T := T) (slotOfDart d))
            simpa [hstart] using hn₁
          · change ¬Occupied (T := T)
              (equiv (T := T) (equiv (T := T) (slotOfDart d)))
            simpa [hstart, hstep₂] using hn₂
          · change ¬Occupied (T := T) (equiv (T := T)
              (equiv (T := T) (equiv (T := T) (slotOfDart d))))
            simpa [hstart, hstep₂, hstep₃] using hn₃

/-- One compressed dart successor lies in the same expanded orbit. -/
theorem sameCycle_slotOfDart_contourSucc (d : GridDirectionalDart T) :
    Equiv.Perm.SameCycle (equiv (T := T))
      (slotOfDart d) (slotOfDart d.contourSucc) := by
  obtain ⟨k, _, _, hk, _⟩ := firstReturn_slotOfDart d
  refine ⟨k, ?_⟩
  simpa [zpow_natCast] using hk

/-- The existing one-cycle theorem for a spanning grid tree lifts to all
occupied slots of the expanded contour. -/
theorem occupied_sameCycle_of_spanningTree
    (hTgrid : T ≤ gridGraph m n) (htree : T.IsTree)
    (a b : GridDirectionalDart T) :
    Equiv.Perm.SameCycle (equiv (T := T)) (slotOfDart a) (slotOfDart b) := by
  have hab := GridDirectionalDart.contourEquiv_sameCycle hTgrid htree a b
  obtain ⟨k, _, hk⟩ := hab.exists_pow_eq'
  have hlift : ∀ r : Nat, ∀ d : GridDirectionalDart T,
      Equiv.Perm.SameCycle (equiv (T := T)) (slotOfDart d)
        (slotOfDart ((GridDirectionalDart.contourEquiv (T := T) ^ r) d)) := by
    intro r
    induction r with
    | zero =>
        intro d
        exact Equiv.Perm.SameCycle.refl _ _
    | succ r ih =>
        intro d
        have hstep := sameCycle_slotOfDart_contourSucc
          ((GridDirectionalDart.contourEquiv (T := T) ^ r) d)
        simpa [pow_succ', GridDirectionalDart.contourEquiv] using (ih d).trans hstep
  simpa [hk] using hlift k a

/-- A nonempty set of compass directions contains one of the four clockwise
positions starting at any given direction. -/
theorem exists_clockwise_mem_of_nonempty (S : Finset GridDirection)
    (hS : S.Nonempty) (e : GridDirection) :
    e ∈ S ∨ e.clockwise ∈ S ∨ e.clockwise.clockwise ∈ S ∨
      e.clockwise.clockwise.clockwise ∈ S := by
  obtain ⟨x, hx⟩ := hS
  fin_cases e <;> fin_cases x <;> simp_all [GridDirection.clockwise]

/-- From any slot at a vertex with a retained direction, at most three local
clockwise moves reach the first occupied slot. -/
theorem exists_first_occupied_iterate
    (s : GridCompassSlot m n)
    (hS : (GridDirectionalDart.directionsAt (T := T) s.1).Nonempty) :
    ∃ k : Nat, k ≤ 3 ∧
      Occupied (T := T) ((equiv (T := T)^[k]) s) ∧
      ∀ j : Nat, j < k →
        ¬Occupied (T := T) ((equiv (T := T)^[j]) s) := by
  rcases s with ⟨v, e⟩
  let S := GridDirectionalDart.directionsAt (T := T) v
  let s₁ : GridCompassSlot m n := (v, e.clockwise)
  let s₂ : GridCompassSlot m n := (v, e.clockwise.clockwise)
  let s₃ : GridCompassSlot m n := (v, e.clockwise.clockwise.clockwise)
  by_cases h₀ : e ∈ S
  · refine ⟨0, by omega, ?_, ?_⟩
    · simpa [Occupied, S] using h₀
    · intro j hj
      omega
  · have hn₀ : ¬Occupied (T := T) (v, e) := by
      simpa [Occupied, S] using h₀
    have hstep₁ : equiv (T := T) (v, e) = s₁ := by
      rw [equiv_apply, succ_of_not_occupied hn₀]
    by_cases h₁ : e.clockwise ∈ S
    · have ho₁ : Occupied (T := T) s₁ := by
        simpa [Occupied, s₁, S] using h₁
      refine ⟨1, by omega, ?_, ?_⟩
      · change Occupied (T := T) (equiv (T := T) (v, e))
        simpa [hstep₁] using ho₁
      · intro j hj
        have : j = 0 := by omega
        subst j
        simpa using hn₀
    · have hn₁ : ¬Occupied (T := T) s₁ := by
        simpa [Occupied, s₁, S] using h₁
      have hstep₂ : equiv (T := T) s₁ = s₂ := by
        rw [equiv_apply, succ_of_not_occupied hn₁]
      by_cases h₂ : e.clockwise.clockwise ∈ S
      · have ho₂ : Occupied (T := T) s₂ := by
          simpa [Occupied, s₂, S] using h₂
        refine ⟨2, by omega, ?_, ?_⟩
        · change Occupied (T := T)
            (equiv (T := T) (equiv (T := T) (v, e)))
          simpa [hstep₁, hstep₂] using ho₂
        · intro j hj
          interval_cases j
          · simpa using hn₀
          · change ¬Occupied (T := T) (equiv (T := T) (v, e))
            simpa [hstep₁] using hn₁
      · have hn₂ : ¬Occupied (T := T) s₂ := by
          simpa [Occupied, s₂, S] using h₂
        have hstep₃ : equiv (T := T) s₂ = s₃ := by
          rw [equiv_apply, succ_of_not_occupied hn₂]
        have h₃ : e.clockwise.clockwise.clockwise ∈ S := by
          rcases exists_clockwise_mem_of_nonempty S hS e with
            h | h | h | h
          · exact (h₀ h).elim
          · exact (h₁ h).elim
          · exact (h₂ h).elim
          · exact h
        have ho₃ : Occupied (T := T) s₃ := by
          simpa [Occupied, s₃, S] using h₃
        refine ⟨3, by omega, ?_, ?_⟩
        · change Occupied (T := T) (equiv (T := T)
            (equiv (T := T) (equiv (T := T) (v, e))))
          simpa [hstep₁, hstep₂, hstep₃] using ho₃
        · intro j hj
          interval_cases j
          · simpa using hn₀
          · change ¬Occupied (T := T) (equiv (T := T) (v, e))
            simpa [hstep₁] using hn₁
          · change ¬Occupied (T := T)
              (equiv (T := T) (equiv (T := T) (v, e)))
            simpa [hstep₁, hstep₂] using hn₂

/-- Every vertex of a nontrivial spanning grid tree has a retained compass
direction. -/
theorem directionsAt_nonempty_of_spanningTree
    (hmn : 2 ≤ m * n) (hT : IsSpanningSubtree (gridGraph m n) T)
    (v : GridVertex m n) :
    (GridDirectionalDart.directionsAt (T := T) v).Nonempty := by
  have hdegree : 0 < T.degree v := tree_degree_pos hmn hT v
  obtain ⟨w, hvw⟩ := (T.degree_pos_iff_exists_adj v).mp hdegree
  obtain ⟨d, hdsource, _⟩ := GridDirectionalDart.exists_of_adj hT.le hvw
  refine ⟨d.direction, GridDirectionalDart.mem_directionsAt.mpr ?_⟩
  exact ⟨d.target, by simpa only [hdsource] using d.step,
    by simpa only [hdsource] using d.adj⟩

/-- Every expanded slot of a nontrivial spanning grid tree shares an orbit
with an occupied directional-dart slot. -/
theorem every_slot_reaches_occupied_of_spanningTree
    (hmn : 2 ≤ m * n) (hT : IsSpanningSubtree (gridGraph m n) T)
    (s : GridCompassSlot m n) :
    ∃ d : GridDirectionalDart T,
      Equiv.Perm.SameCycle (equiv (T := T)) s (slotOfDart d) := by
  obtain ⟨k, _, hk, _⟩ := exists_first_occupied_iterate s
    (directionsAt_nonempty_of_spanningTree hmn hT s.1)
  let d := GridDirectionalDart.ofDirectionMem (T := T)
    ((equiv (T := T)^[k]) s).1 ((equiv (T := T)^[k]) s).2 hk
  refine ⟨d, k, ?_⟩
  simp [zpow_natCast, slotOfDart, d]

/-- The expanded slot carrying an outer boundary port. -/
def outerPortSlot {n : Nat} {T : SimpleGraph (GridVertex n n)}
    [DecidableRel T.Adj]
    (p : GridCotreeOuterPort T) : GridCompassSlot n n :=
  (p.vertex, p.outwardDirection)

theorem outerPortSlot_not_occupied {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (p : GridCotreeOuterPort T) :
    ¬Occupied (T := T) (outerPortSlot p) :=
  GridCotreeOuterPort.outwardDirection_notMem_directionsAt p

theorem outerPortSlot_injective {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj] :
    Function.Injective (outerPortSlot (T := T)) := by
  intro p q h
  apply OuterBoundaryPort.ext
  · exact congrArg Prod.fst h
  · apply OuterBoundarySide.outwardDirection_injective
    exact congrArg Prod.snd h

/-- Slot encoded by a refined outer-port contour occurrence. -/
def slotOfOccurrence {n : Nat} {T : SimpleGraph (GridVertex n n)}
    [DecidableRel T.Adj] (o : GridOuterPortContourOccurrence T) :
    GridCompassSlot n n :=
  (o.dart.source, o.crossedDirection)

@[simp] theorem outerPortSlot_eq_slotOf_contourOccurrence {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (p : GridCotreeOuterPort T) :
    outerPortSlot p =
      slotOfOccurrence (GridCotreeOuterPort.contourOccurrence hn hT p) := by
  simp [outerPortSlot, slotOfOccurrence, GridCotreeOuterPort.contourOccurrence]

/-- To prove that the expanded permutation has one orbit, it suffices to prove
that all occupied dart slots share an orbit and every slot reaches such an
occupied orbit. -/
theorem sameCycle_of_occupied_sameCycle_of_every_slot_reaches
    (hoccupied : ∀ a b : GridDirectionalDart T,
      Equiv.Perm.SameCycle (equiv (T := T)) (slotOfDart a) (slotOfDart b))
    (hreaches : ∀ s : GridCompassSlot m n, ∃ d : GridDirectionalDart T,
      Equiv.Perm.SameCycle (equiv (T := T)) s (slotOfDart d))
    (s t : GridCompassSlot m n) :
    Equiv.Perm.SameCycle (equiv (T := T)) s t := by
  obtain ⟨a, ha⟩ := hreaches s
  obtain ⟨b, hb⟩ := hreaches t
  exact ha.trans ((hoccupied a b).trans hb.symm)

/-- For a spanning tree, global expanded cyclicity is reduced exactly to
reachability of an occupied dart slot from every expanded slot. -/
theorem sameCycle_of_spanningTree_of_every_slot_reaches
    (hTgrid : T ≤ gridGraph m n) (htree : T.IsTree)
    (hreaches : ∀ s : GridCompassSlot m n, ∃ d : GridDirectionalDart T,
      Equiv.Perm.SameCycle (equiv (T := T)) s (slotOfDart d))
    (s t : GridCompassSlot m n) :
    Equiv.Perm.SameCycle (equiv (T := T)) s t :=
  sameCycle_of_occupied_sameCycle_of_every_slot_reaches
    (occupied_sameCycle_of_spanningTree hTgrid htree) hreaches s t

/-- The expanded contour of any nontrivial spanning rectangular grid tree has
one orbit. -/
theorem equiv_sameCycle_of_spanningTree
    (hmn : 2 ≤ m * n) (hT : IsSpanningSubtree (gridGraph m n) T)
    (s t : GridCompassSlot m n) :
    Equiv.Perm.SameCycle (equiv (T := T)) s t :=
  sameCycle_of_spanningTree_of_every_slot_reaches hT.le hT.isTree
    (every_slot_reaches_occupied_of_spanningTree hmn hT) s t

/-- The expanded contour of a nontrivial spanning square-grid tree has one
orbit. -/
theorem equiv_sameCycle_of_spanningSquareTree {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (s t : GridCompassSlot n n) :
    Equiv.Perm.SameCycle (equiv (T := T)) s t :=
  equiv_sameCycle_of_spanningTree (by nlinarith) hT s t

/-- The expanded permutation of a nontrivial spanning square-grid tree is a
single nontrivial cycle. -/
theorem equiv_isCycle_of_spanningSquareTree {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T) :
    Equiv.Perm.IsCycle (equiv (T := T)) := by
  let v : GridVertex n n := (⟨0, by omega⟩, ⟨0, by omega⟩)
  obtain ⟨e, he⟩ := directionsAt_nonempty_of_spanningTree
    (T := T) (by nlinarith) hT v
  let d := GridDirectionalDart.ofDirectionMem (T := T) v e he
  refine ⟨slotOfDart d, ?_, ?_⟩
  · intro hfixed
    rw [equiv_apply, succ_slotOfDart] at hfixed
    have htarget : d.target = d.source := by
      exact congrArg Prod.fst hfixed
    exact T.loopless d.source (htarget ▸ d.adj)
  · intro y _
    exact equiv_sameCycle_of_spanningSquareTree hn hT (slotOfDart d) y

/-! ### Expanded shore intervals -/

/-- Every expanded target-shore slot occurs after the dart entry and no later
than its reverse-dart exit. -/
theorem mem_targetShore_exists_pow_through_exit {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (d : GridDirectionalDart T) {slot : GridCompassSlot n n}
    (hslot : slot ∈ expandedTargetShoreSlots d) :
    ∃ k, 0 < k ∧ k ≤ permForwardDistance (equiv (T := T)) (slotOfDart d)
        (slotOfDart d.reverse)
        (equiv_sameCycle_of_spanningSquareTree hn hT _ _) ∧
      ((equiv (T := T)) ^ k) (slotOfDart d) = slot := by
  rw [← mem_permClosedForwardInterval_iff]
  apply Equiv.Perm.mem_closedForwardInterval_of_unique_entry_exit
    (equiv (T := T)) (expandedTargetShoreSlots d)
      (equiv_isCycle_of_spanningSquareTree hn hT)
      (fun x => equiv_sameCycle_of_spanningSquareTree hn hT _ x)
  · rw [mem_expandedTargetShoreSlots]
    exact GridDirectionalDart.source_notMem_targetShoreVertices hT.isAcyclic d
  · simp [equiv_apply, succ_slotOfDart]
  · intro x hx
    simpa [equiv_apply] using
      succ_notMem_expandedTargetShoreSlots_iff_of_mem hT.isAcyclic d x hx
  · intro x hx
    simpa [equiv_apply] using
      succ_mem_expandedTargetShoreSlots_iff_of_notMem hT.isAcyclic d x hx
  · exact hslot

/-- An expanded fundamental shore is exactly the closed forward contour
segment after its entry through its exit. -/
theorem expandedTargetShoreSlots_eq_closedForwardInterval {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (d : GridDirectionalDart T) :
    expandedTargetShoreSlots d =
      permClosedForwardInterval (equiv (T := T)) (slotOfDart d)
        (slotOfDart d.reverse)
        (equiv_sameCycle_of_spanningSquareTree hn hT _ _) := by
  apply Equiv.Perm.eq_closedForwardInterval_of_unique_entry_exit
    (equiv (T := T)) (expandedTargetShoreSlots d)
      (equiv_isCycle_of_spanningSquareTree hn hT)
      (fun x => equiv_sameCycle_of_spanningSquareTree hn hT _ x)
  · rw [mem_expandedTargetShoreSlots]
    exact GridDirectionalDart.source_notMem_targetShoreVertices hT.isAcyclic d
  · simp [equiv_apply, succ_slotOfDart]
  · intro x hx
    simpa [equiv_apply] using
      succ_notMem_expandedTargetShoreSlots_iff_of_mem hT.isAcyclic d x hx
  · intro x hx
    simpa [equiv_apply] using
      succ_mem_expandedTargetShoreSlots_iff_of_notMem hT.isAcyclic d x hx

/-- Every positive expanded-contour iterate after the entry, through the exit
slot itself, is based in the target shore. -/
theorem pow_mem_expandedTargetShoreSlots_through_exit {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (d : GridDirectionalDart T) {k : Nat} (hkpos : 0 < k)
    (hkle : k ≤ permForwardDistance (equiv (T := T)) (slotOfDart d)
      (slotOfDart d.reverse)
      (equiv_sameCycle_of_spanningSquareTree hn hT _ _)) :
    ((equiv (T := T)) ^ k) (slotOfDart d) ∈
      expandedTargetShoreSlots d := by
  apply Equiv.Perm.pow_mem_of_pos_le_permForwardDistance_of_unique_exit
    (equiv (T := T)) (expandedTargetShoreSlots d)
      (equiv_sameCycle_of_spanningSquareTree hn hT _ _)
  · simp [equiv_apply, succ_slotOfDart]
  · intro slot hin
    simpa [equiv_apply] using
      succ_notMem_expandedTargetShoreSlots_iff_of_mem hT.isAcyclic d slot hin
  · exact hkpos
  · exact hkle

/-- The corrected entry-to-exit open interval consists entirely of expanded
slots based in the target shore. -/
theorem permOpenForwardInterval_entry_exit_subset_targetShore {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (d : GridDirectionalDart T) :
    permOpenForwardInterval (equiv (T := T)) (slotOfDart d)
      (slotOfDart d.reverse)
      (equiv_sameCycle_of_spanningSquareTree hn hT _ _) ⊆
        expandedTargetShoreSlots d := by
  apply Equiv.Perm.permOpenForwardInterval_subset_of_unique_exit
    (equiv (T := T)) (expandedTargetShoreSlots d)
      (equiv_sameCycle_of_spanningSquareTree hn hT _ _)
  · simp [equiv_apply, succ_slotOfDart]
  · intro slot hin
    simpa [equiv_apply] using
      succ_notMem_expandedTargetShoreSlots_iff_of_mem hT.isAcyclic d slot hin

/-- Every positive expanded-contour iterate after the exit, through the next
entry slot itself, is based outside the target shore. -/
theorem pow_notMem_expandedTargetShoreSlots_through_entry {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (d : GridDirectionalDart T) {k : Nat} (hkpos : 0 < k)
    (hkle : k ≤ permForwardDistance (equiv (T := T))
      (slotOfDart d.reverse) (slotOfDart d)
      (equiv_sameCycle_of_spanningSquareTree hn hT _ _)) :
    ((equiv (T := T)) ^ k) (slotOfDart d.reverse) ∉
      expandedTargetShoreSlots d := by
  apply Equiv.Perm.pow_notMem_of_pos_le_permForwardDistance_of_unique_entry
    (equiv (T := T)) (expandedTargetShoreSlots d)
      (equiv_sameCycle_of_spanningSquareTree hn hT _ _)
  · rw [equiv_apply, mem_expandedTargetShoreSlots, succ_slotOfDart]
    simpa [GridDirectionalDart.reverse] using
      GridDirectionalDart.source_notMem_targetShoreVertices hT.isAcyclic d
  · intro slot hout
    simpa [equiv_apply] using
      succ_mem_expandedTargetShoreSlots_iff_of_notMem hT.isAcyclic d slot hout
  · exact hkpos
  · exact hkle

/-- The complementary exit-to-entry open interval consists entirely of slots
based outside the target shore. -/
theorem disjoint_permOpenForwardInterval_exit_entry_targetShore {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hn : 2 ≤ n) (hT : IsSpanningSubtree (gridGraph n n) T)
    (d : GridDirectionalDart T) :
    Disjoint
      (permOpenForwardInterval (equiv (T := T)) (slotOfDart d.reverse)
        (slotOfDart d) (equiv_sameCycle_of_spanningSquareTree hn hT _ _))
      (expandedTargetShoreSlots d) := by
  apply Equiv.Perm.disjoint_permOpenForwardInterval_of_unique_entry
    (equiv (T := T)) (expandedTargetShoreSlots d)
      (equiv_sameCycle_of_spanningSquareTree hn hT _ _)
  · rw [equiv_apply, mem_expandedTargetShoreSlots, succ_slotOfDart]
    simpa [GridDirectionalDart.reverse] using
      GridDirectionalDart.source_notMem_targetShoreVertices hT.isAcyclic d
  · intro slot hout
    simpa [equiv_apply] using
      succ_mem_expandedTargetShoreSlots_iff_of_notMem hT.isAcyclic d slot hout

end GridExpandedContour

end GridGraphs
