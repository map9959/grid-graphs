import GridGraphs.ResidueZeroTransitions

/-!
# The residue-zero phase word

This file records the six forms of adjacent rows in the phase word and proves
that the recursive construction has only those transitions.
-/

namespace GridGraphs

/-- The six allowed forms of consecutive rows in a phase word, including the
parameter bounds needed to use their local transition lemmas. -/
inductive ValidPhaseTransition (k : Nat) : PhaseRow → PhaseRow → Prop where
  | ordinaryPred (ha0 : 0 < a) (ha : a < k) :
      ValidPhaseTransition k (.ordinary a) (.ordinary (a - 1))
  | ordinarySucc (ha : a + 1 < k) :
      ValidPhaseTransition k (.ordinary a) (.ordinary (a + 1))
  | ordinarySeamSame (ha : a < k) :
      ValidPhaseTransition k (.ordinary a) (.seam a)
  | ordinarySeamSucc (ha : a + 1 < k) :
      ValidPhaseTransition k (.ordinary a) (.seam (a + 1))
  | seamOrdinaryPred (ha0 : 0 < a) (ha : a < k) :
      ValidPhaseTransition k (.seam a) (.ordinary (a - 1))
  | seamOrdinarySame (ha : a < k) :
      ValidPhaseTransition k (.seam a) (.ordinary a)

/-- Increasing the ambient width preserves a valid transition. -/
theorem ValidPhaseTransition.mono {k k' : Nat} (hkk : k ≤ k')
    {top bottom : PhaseRow} (h : ValidPhaseTransition k top bottom) :
    ValidPhaseTransition k' top bottom := by
  cases h with
  | ordinaryPred ha0 ha => exact .ordinaryPred ha0 (by omega)
  | ordinarySucc ha => exact .ordinarySucc (by omega)
  | ordinarySeamSame ha => exact .ordinarySeamSame (by omega)
  | ordinarySeamSucc ha => exact .ordinarySeamSucc (by omega)
  | seamOrdinaryPred ha0 ha => exact .seamOrdinaryPred ha0 (by omega)
  | seamOrdinarySame ha => exact .seamOrdinarySame (by omega)

/-- The first row of `B_(7+t)` is `R_(t+4)`. -/
@[simp] theorem phaseRowsFrom_first (t : Nat) :
    (phaseRowsFrom t).head? = some (.ordinary (t + 4)) := by
  cases t <;> simp [phaseRowsFrom, phaseRowsBase]

/-- The final row of `B_(7+t)` is `R_(t+6)`. -/
@[simp] theorem phaseRowsFrom_last (t : Nat) :
    (phaseRowsFrom t).getLast? = some (.ordinary (t + 6)) := by
  cases t with
  | zero => simp [phaseRowsFrom, phaseRowsBase]
  | succ t =>
      simp only [phaseRowsFrom, List.cons_append, List.nil_append,
        List.getLast?_cons, List.getLast?_append]
      congr 2

/-- The base word `B_7` has only valid transitions. -/
theorem phaseRowsBase_valid :
    (phaseRowsBase.IsChain (ValidPhaseTransition 7)) := by
  simp only [phaseRowsBase, List.isChain_cons_cons, List.IsChain.singleton]
  repeat' apply And.intro
  all_goals first
    | trivial
    | exact .ordinaryPred (by omega) (by omega)
    | exact .ordinarySucc (by omega)
    | exact .ordinarySeamSame (by omega)
    | exact .ordinarySeamSucc (by omega)
    | exact .seamOrdinaryPred (by omega) (by omega)
    | exact .seamOrdinarySame (by omega)

/-- Every transition in `B_(7+t)` is valid at its current width. -/
theorem phaseRowsFrom_valid (t : Nat) :
    (phaseRowsFrom t).IsChain (ValidPhaseTransition (7 + t)) := by
  induction t with
  | zero => simpa [phaseRowsFrom] using phaseRowsBase_valid
  | succ t ih =>
      have hold : (phaseRowsFrom t).IsChain (ValidPhaseTransition (7 + (t + 1))) :=
        ih.imp fun _ _ h => h.mono (by omega)
      have hprefix :
          ([.ordinary (t + 5), .seam (t + 5)] : List PhaseRow).IsChain
            (ValidPhaseTransition (7 + (t + 1))) := by
        simp only [List.isChain_pair]
        exact .ordinarySeamSame (by omega)
      have hleft :
          (([.ordinary (t + 5), .seam (t + 5)] : List PhaseRow) ++
              phaseRowsFrom t).IsChain
            (ValidPhaseTransition (7 + (t + 1))) := by
        apply hprefix.append hold
        intro x hx y hy
        simp at hx hy
        subst x
        subst y
        have h := ValidPhaseTransition.seamOrdinaryPred (a := t + 5)
          (k := 7 + (t + 1)) (by omega) (by omega)
        simpa only [show t + 5 - 1 = t + 4 by omega] using h
      rw [phaseRowsFrom]
      apply hleft.append
      · exact .singleton _
      · intro x hx y hy
        have hleftLast :
            (([.ordinary (t + 5), .seam (t + 5)] : List PhaseRow) ++
              phaseRowsFrom t).getLast? = some (.ordinary (t + 6)) := by
          rw [List.getLast?_append, phaseRowsFrom_last]
          rfl
        rw [hleftLast] at hx
        simp at hx hy
        subst x
        subst y
        have h := ValidPhaseTransition.ordinarySucc (a := t + 6)
          (k := 7 + (t + 1)) (by omega)
        simpa only [show t + 6 + 1 = t + 7 by omega] using h

/-- The first row of `B_k` is `R_(k-3)`. -/
theorem phaseRows_first (k : Nat) (hk : 7 ≤ k) :
    (phaseRows k).head? = some (.ordinary (k - 3)) := by
  rw [phaseRows, if_pos hk, phaseRowsFrom_first]
  congr 2
  omega

/-- The final row of `B_k` is `R_(k-1)`. -/
theorem phaseRows_last (k : Nat) (hk : 7 ≤ k) :
    (phaseRows k).getLast? = some (.ordinary (k - 1)) := by
  rw [phaseRows, if_pos hk, phaseRowsFrom_last]
  congr 2
  omega

/-- Every adjacent pair in `B_k` is one of the six valid transition classes. -/
theorem phaseRows_adjacent_valid (k : Nat) (hk : 7 ≤ k) (i : Nat)
    (hi : i + 1 < (phaseRows k).length) :
    ValidPhaseTransition k ((phaseRows k)[i]'(by omega))
      ((phaseRows k)[i + 1]'hi) := by
  have hchain : (phaseRows k).IsChain (ValidPhaseTransition k) := by
    rw [phaseRows, if_pos hk]
    have h := phaseRowsFrom_valid (k - 7)
    simpa only [show 7 + (k - 7) = k by omega] using h
  exact (List.isChain_iff_getElem.mp hchain) i hi

end GridGraphs
