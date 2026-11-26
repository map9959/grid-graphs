import GridGraphs.Constructions.ResidueTwo.LowerTurnCheck

namespace GridGraphs.ResidueTwoLower.Poly

private theorem reduced_iff (p : Formula) {cs t i j} (h : Holds cs t i j) :
    (reduced cs p).denote t i j ↔ p.denote t i j := by
  induction p with
  | yes | no => rfl
  | both a b ha hb | either a b ha hb => simp [reduced,ha,hb,Formula.denote]
  | test a =>
    simp only [reduced]
    split
    · rename_i pos; obtain ⟨x,hx,e⟩ := List.any_eq_true.mp pos
      simp [Formula.denote,Lin.entails_sound e _ _ _ (h x hx)]
    · split
      · rename_i neg; obtain ⟨x,hx,e⟩ := List.any_eq_true.mp neg
        have z := (Lin.neg_nonneg a t i j).mp (Lin.entails_sound e _ _ _ (h x hx))
        simp [Formula.denote,z]
      · rfl

theorem solve_sound (fuel) {cs p t i j} (hc : Holds cs t i j) (hp : p.denote t i j) :
    solve fuel cs p = false := by
  induction fuel generalizing cs p with
  | zero => exact impossible_sound hc
  | succ f ih =>
    have q := (reduced_iff p hc).mpr hp
    unfold solve
    generalize eq : reduced cs p = g at q ⊢
    have branch : (impossible cs || (solve f ((firstAtom g)::cs) g &&
        solve f ((firstAtom g).neg::cs) g)) = false := by
      rw [impossible_sound hc,Bool.false_or]
      by_cases h : 0 ≤ (firstAtom g).val t i j
      · have c : Holds (firstAtom g::cs) t i j := fun x hx =>
          (List.mem_cons.mp hx).elim (fun e => e ▸ h) (hc x)
        simp [ih c q]
      · have c : Holds ((firstAtom g).neg::cs) t i j := fun x hx =>
          (List.mem_cons.mp hx).elim (fun e => e ▸ (Lin.neg_nonneg _ _ _ _).mpr h) (hc x)
        simp [ih c q]
    cases g with
    | no => exact q.elim
    | yes => exact fallback_sound hc
    | _ => exact branch

end GridGraphs.ResidueTwoLower.Poly
