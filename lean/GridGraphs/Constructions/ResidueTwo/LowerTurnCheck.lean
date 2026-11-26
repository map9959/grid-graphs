import GridGraphs.Constructions.ResidueTwo.LowerTurnPoly

namespace GridGraphs.ResidueTwoLower.Poly

def Formula.denote (t i j : ℤ) : Formula → Prop
  | .yes => True | .no => False | .test a => 0 ≤ a.val t i j
  | .both p q => p.denote t i j ∧ q.denote t i j
  | .either p q => p.denote t i j ∨ q.denote t i j

@[simp] theorem Formula.band_denote (a b : Formula) (t i j) :
    (a.band b).denote t i j ↔ a.denote t i j ∧ b.denote t i j := by
  cases a <;> cases b <;> simp [band,denote]

@[simp] theorem Formula.bor_denote (a b : Formula) (t i j) :
    (a.bor b).denote t i j ↔ a.denote t i j ∨ b.denote t i j := by
  cases a <;> cases b <;> simp [bor,denote]

@[simp] theorem Formula.denote_neg (p : Formula) (t i j) :
    p.neg.denote t i j ↔ ¬p.denote t i j := by
  induction p <;> simp_all [neg,denote] <;> tauto

/-- Unsatisfiability search. A timeout or incomplete arithmetic
elimination returns false and can never admit a certificate. -/

theorem refute_sound (fuel) {t i j} {cs ps} (h : Holds cs t i j)
    (ok : ∀ p ∈ ps, p.denote t i j) : refute fuel cs ps = false := by
  induction fuel generalizing cs ps with
  | zero => cases ps <;> exact impossible_sound h
  | succ f ih =>
    cases ps with
    | nil => exact impossible_sound h
    | cons p ps =>
      have hp := ok p (by simp)
      have tail (p) (hm : p∈ps) := ok p (by simp [hm])
      cases p with
      | yes => exact ih h tail
      | no => exact hp.elim
      | test a =>
        have ha : Holds (a::cs) t i j := by
          intro x hx; rcases List.mem_cons.mp hx with rfl|hx
          · exact hp
          · exact h x hx
        exact ih ha tail
      | both a b =>
        apply ih h
        intro x hx
        rcases List.mem_cons.mp hx with rfl|hx
        · exact hp.1
        rcases List.mem_cons.mp hx with rfl|hx
        · exact hp.2
        exact tail _ hx
      | either a b =>
        rcases hp with ha|hb
        · have E := ih h (ps := a::ps) (by simpa only [List.forall_mem_cons] using And.intro ha tail)
          simp [refute,E,impossible_sound h]
        · have E := ih h (ps := b::ps) (by simpa only [List.forall_mem_cons] using And.intro hb tail)
          simp [refute,E,impossible_sound h]

end GridGraphs.ResidueTwoLower.Poly
