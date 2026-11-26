import GridGraphs.ResidueTwoUpper.ExceptionalFrameTransport

namespace GridGraphs.ResidueTwoUpper.Exceptional.Frame
open ResidueZero Stencil Finset

private theorem same {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (v : GridVertex n n)
    (a : origins n) (q : Fin 9) (eq : coord v=coord a+offset q) (b : Bool) :
    starRank n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) b q =
      patchRank n (coord a) (maskAt F a) b q := by
  have ok := coord_inside a
  rw [Nat.cast_sub hn] at ok
  norm_num1 at ok
  have ev := physical_incidence_key F a.1 a.2 (by have := a.1.isLt; omega)
    (by have := a.2.isLt; omega) q 0
  have ident : ∀ (q : Fin 9) (nb : Fin 16) (m : Fin 512),
      patchQ 0 q=q ∧ rotBits 0 nb=nb ∧ rotMask 0 m=m := by native_decide
  obtain ⟨q0,nb0,m0⟩ := ident q ⟨neighbours F (coord v),code_lt _⟩ (maskAt F a)
  change localEvent (patchQ 0 q) (marked F (coord a+offset q)).toNat
    (rotBits 0 (neighbours F (coord a+offset q))) = localEvent (patchQ 0 q)
      (bit (rotMask 0 (maskAt F a)) (patchQ 0 q)) (patchNbr (rotMask 0 (maskAt F a)) (patchQ 0 q)) at ev
  rw [←eq,q0,marked_at,nb0,m0] at ev
  change localEvent q (decide (v∈F)).toNat (neighbours F (coord v))=_ at ev
  have back : coord v-offset q=coord a := sub_eq_iff_eq_add.mpr eq
  unfold starRank patchRank
  rw [back,if_pos ok,ev,eq]

def rankAt {n} (F : Finset (GridVertex n n)) (own : Bool) : occurrence n → Fin 9 → Nat :=
  Sum.elim (fun v => starRank n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) (!own))
    (fun a => patchRank n (coord a) (maskAt F a) own)

theorem opposite {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (x : occurrence n) (q : Fin 9)
    (pos : 0<rankAt F false x q) : ∃ y, rankAt F true y q=rankAt F false x q := by
  cases x with
  | inl v =>
    have h : inside ((n:Int)-2) (coord v-offset q) := by
      by_contra bad
      simp [rankAt,starRank,bad] at pos
    have h' : inside (n-2:Nat) (coord v-offset q) := by simpa [Nat.cast_sub hn] using h
    let a := onSite _ h'
    have eq : coord v=coord a+offset q := by rw [show coord a=_ from coord_onSite ..]; simp
    exact ⟨Sum.inr a,(same hn F v a q eq true).symm⟩
  | inr a =>
    have h : inside n (coord a+offset q) := by
      have h₁ := a.1.isLt; have h₂ := a.2.isLt; have h₃ := q.isLt
      have h₄ : q.val/3<3 := by omega
      have h₅ : q.val%3<3 := Nat.mod_lt _ (by decide)
      have ha : inside n ((a.1.val:Int)+(q.val/3:Nat),(a.2.val:Int)+(q.val%3:Nat)) := by
        simp only [inside,Bool.and_eq_true,decide_eq_true_eq]; omega
      exact ha
    let v := onSite _ h
    exact ⟨Sum.inl v,same hn F v a q (coord_onSite ..) false⟩

theorem eliminate {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (good : occurrence n → Bool)
    (h : ∀ x, traceOK (rankAt F true x) (rankAt F false x) (good x)) :
    ∀ x, good x := by
  have none (r : Nat) : ∀ x q, rankAt F true x q=r → r≠0 → False := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro x q eq pos
      obtain ⟨j,low,lt⟩ := (h x).1 q (eq ▸ pos)
      obtain ⟨y,other⟩ := opposite hn F x j low
      exact ih _ (lt.trans_eq eq) y j other low.ne'
  intro x
  by_contra bad
  obtain ⟨j,val⟩ := (h x).2 (by simpa using bad)
  obtain ⟨y,other⟩ := opposite hn F x j val
  exact none _ y j other val.ne'

end GridGraphs.ResidueTwoUpper.Exceptional.Frame
