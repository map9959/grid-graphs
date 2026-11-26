import GridGraphs.Constructions.ResidueTwo.LowerTurnBoundary

namespace GridGraphs.ResidueTwoLower.Turn

/-- A set of states of a directed forced-edge walk. -/
abbrev Layer := Pt → Dir → Prop

/-- Closure of layer `q`: a straight continuation stays in `q`; a
perpendicular continuation from `p` forces the preceding edge into `q`. -/
def Step (n : Nat) (m : Mask) (p q : Layer) : Prop :=
  (∀ v d, forced n m v d → q (advance v d) d → q v d) ∧
  (∀ v d e, e=turnL d ∨ e=turnR d → forced n m v d → p (advance v d) e → q v d)

private noncomputable def weight (layers : List Layer) (v : Pt) (d : Dir) : Nat := by
  classical
  exact (layers.filter fun p => p v d).length

private theorem weight_mono (ls : List Layer) {u v d e}
    (h : ∀ p ∈ ls, p u e → p v d) : weight ls u e ≤ weight ls v d := by
  classical
  unfold weight
  induction ls with
  | nil => rfl
  | cons p ps ih =>
    have tail := ih fun x hx => h x (by simp [hx])
    have head := h p (by simp)
    by_cases hu : p u e <;> by_cases hv : p v d <;> simp_all <;> omega

private theorem weight_cons_hit (p : Layer) (ps : List Layer) {u e} (h : p u e) :
    weight (p::ps) u e = weight ps u e + 1 := by classical simp [weight,h]

private theorem weight_empty_end (ps : List Layer) (u e) :
    weight (ps ++ [fun _ _ => False]) u e = weight ps u e := by classical simp [weight]

/-- The terminal layer is empty, so a turn drops the count of occupied
layers strictly. No nesting or exactness condition on the layers is needed. -/
theorem routes_of_layers (n : Nat) (m : Mask) (ps : List Layer)
    (h : List.Forall₂ (Step n m) (forced n m :: ps) (ps ++ [fun _ _ => False]))
    (r c : Fin (n-1)) : (holeDual n m).Reachable (.cell r c) .out := by
  apply routes_of_turn_rank m (weight ps)
  · intro v d f _
    apply weight_mono
    intro q hq
    have each {as bs : List Layer} (hh : List.Forall₂ (Step n m) as bs)
        (q : Layer) (hq : q ∈ bs) : q (advance v d) d → q v d := by
      induction hh with
      | nil => simp at hq
      | cons ab rest ih =>
        rcases List.mem_cons.mp hq with rfl|hq
        · exact ab.1 v d f
        · exact ih hq
    exact each h q (by simp [hq])
  · intro v d e he f f'
    have compare {as bs : List Layer} (hh : List.Forall₂ (Step n m) as bs) :
        weight as (advance v d) e ≤ weight bs v d := by
      classical
      induction hh with
      | nil => rfl
      | @cons a b as bs ab rest ih =>
        have imp := ab.2 v d e he f
        by_cases ha : a (advance v d) e <;> by_cases hb : b v d <;>
          simp_all [weight] <;> omega
    have g := compare h
    rw [weight_cons_hit _ _ f',weight_empty_end] at g
    omega

end GridGraphs.ResidueTwoLower.Turn
