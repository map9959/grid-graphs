import GridGraphs.LocalizedHallRouting

/-!
# Ranked transition ownership

This module records nonlocal debt propagation without identifying states that
use the same geometric transition.  States are occurrence-labelled by their
originating debt, while a strictly decreasing rank makes every chain terminate.
-/

namespace GridGraphs

/-- An occurrence-indexed transition system.  Distinct states may carry the
same transition label; this is essential when geometric transition chains
reconverge without merging their debts. -/
structure RankedTransitionSystem (Debt State Transition Terminal : Type*) where
  next : State → Option State
  rank : State → Nat
  rank_next : ∀ {x y}, next x = some y → rank y < rank x
  origin : State → Debt
  origin_next : ∀ {x y}, next x = some y → origin y = origin x
  transition : State → Option Transition
  transition_some_iff_next_some : ∀ x, transition x ≠ none ↔ next x ≠ none
  terminal : State → Option Terminal
  terminal_some_iff_next_none : ∀ x, terminal x ≠ none ↔ next x = none

namespace RankedTransitionSystem

variable {Debt State Transition Terminal : Type*}
    (S : RankedTransitionSystem Debt State Transition Terminal)

/-- One occurrence-preserving propagation step. -/
def Step (x y : State) : Prop := S.next x = some y

/-- Terminal states remain occurrence-labelled even when their eventual
geometric resources coincide. -/
def TerminalState := {x : State // S.next x = none}

/-- The debt provenance is unchanged along any finite transition chain. -/
theorem origin_eq_of_reflTransGen {x y : State}
    (hxy : Relation.ReflTransGen S.Step x y) :
    S.origin y = S.origin x := by
  induction hxy with
  | refl => rfl
  | tail hxy hstep ih =>
      exact (S.origin_next hstep).trans ih

/-- Every ranked propagation chain reaches a terminal occurrence while
retaining the original debt label. -/
theorem exists_terminal_same_origin (x : State) :
    ∃ y t, Relation.ReflTransGen S.Step x y ∧
      S.terminal y = some t ∧ S.origin y = S.origin x := by
  suffices h : ∀ k x, S.rank x = k →
      ∃ y t, Relation.ReflTransGen S.Step x y ∧
        S.terminal y = some t ∧ S.origin y = S.origin x by
    exact h (S.rank x) x rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro x hx
      cases hnext : S.next x with
      | none =>
          have hterminal : S.terminal x ≠ none :=
            (S.terminal_some_iff_next_none x).2 hnext
          obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hterminal
          exact ⟨x, t, Relation.ReflTransGen.refl, ht, rfl⟩
      | some y =>
          have hrank : S.rank y < k := by
            rw [← hx]
            exact S.rank_next hnext
          obtain ⟨z, t, hyz, ht, horigin⟩ :=
            ih (S.rank y) hrank y rfl
          refine ⟨z, t, Relation.ReflTransGen.head hnext hyz, ht, ?_⟩
          exact horigin.trans (S.origin_next hnext)

/-- Occurrence-valued form of `exists_terminal_same_origin`.  No quotient by a
transition label or terminal resource is taken. -/
theorem exists_terminalState_same_origin (x : State) :
    ∃ y : S.TerminalState,
      Relation.ReflTransGen S.Step x y.1 ∧ S.origin y.1 = S.origin x := by
  obtain ⟨y, t, hxy, ht, horigin⟩ := S.exists_terminal_same_origin x
  have hterminal : S.terminal y ≠ none := by simp [ht]
  exact ⟨⟨y, (S.terminal_some_iff_next_none y).1 hterminal⟩, hxy, horigin⟩

/-- Terminal occurrences reached from starts retain any owner determined by
the originating debt. -/
theorem exists_terminal_same_owner {Owner : Type*}
    (ownerDebt : Debt → Owner) (x : State) :
    ∃ y t, Relation.ReflTransGen S.Step x y ∧
      S.terminal y = some t ∧
      ownerDebt (S.origin y) = ownerDebt (S.origin x) := by
  obtain ⟨y, t, hxy, ht, horigin⟩ := S.exists_terminal_same_origin x
  exact ⟨y, t, hxy, ht, congrArg ownerDebt horigin⟩

end RankedTransitionSystem

end GridGraphs
