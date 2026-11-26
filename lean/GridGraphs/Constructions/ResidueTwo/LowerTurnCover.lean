import GridGraphs.Constructions.ResidueTwo.LowerTurnMask

namespace GridGraphs.ResidueTwoLower.Poly

private def bound (n : Exp) := Region.both (.ge .i 0) (.both (ltE .i n)
  (.both (.ge .j 0) (ltE .j n)))

def coverTrial (ch : Chart) (n : Exp) (mask : Region) (d : Turn.Dir) (atEnd : Bool) :
    List Lit :=
  let o := offset d
  [⟨.ge .t 0,0,0,true⟩,⟨bound n,0,0,true⟩,⟨bound n,o.1,o.2,true⟩,
   ⟨mask,if atEnd then o.1 else 0,if atEnd then o.2 else 0,true⟩,
   ⟨Reg ch 0 d,0,0,false⟩]

def coverOK (ch : Chart) (n : Exp) (mask : Region) :=
  dirs.all fun d => check (coverTrial ch n mask d false) &&
    check (coverTrial ch n mask d true)

theorem cover_sound {ch : Chart} {n : Nat} {width : Exp} {mask : Region} {t : Nat} (m : Mask)
    (width_ok : ∀ i j, width.eval t i j=n)
    (mark_ok : ∀ (i j : Nat), i<n → j<n → m i j=true → mask.eval t i j)
    (ok : coverOK ch width mask=true) (v d) (h : Turn.forced n m v d) :
    allowed ch 0 d t v := by
  have bnd (u : Turn.Pt) (hu : Turn.onBoard n u) : (bound width).eval t u.1 u.2 := by
    simpa [bound,ltE,Region.eval,Exp.eval,width_ok,Turn.onBoard] using hu
  have mark (u : Turn.Pt) (hu : Turn.onBoard n u) (a : m u.1.toNat u.2.toNat=true) :
      mask.eval t u.1 u.2 := by
    obtain ⟨_,_,_,_⟩ := hu
    simpa [Int.toNat_of_nonneg,show 0 ≤ u.1 by omega,show 0 ≤ u.2 by omega] using
      mark_ok u.1.toNat u.2.toNat (by omega) (by omega) a
  obtain ⟨bv,bw,edge⟩ := h
  have front := bnd v bv
  have back := bnd _ bw
  have test := (List.all_eq_true.mp ok) d (by cases d <;> simp [dirs])
  rw [Bool.and_eq_true] at test
  by_contra neg
  simp only [Bool.or_eq_true] at edge
  rcases edge with a|a
  · have yes := mark _ bv a
    apply check_sound test.1 t v.1 v.2
    cases d <;> simp_all [coverTrial,Lit.Holds,allowed,Turn.advance,offset,Region.eval,Exp.eval,
      sub_eq_add_neg]
  · have yes := mark _ bw a
    apply check_sound test.2 t v.1 v.2
    cases d <;> simp_all [coverTrial,Lit.Holds,allowed,Turn.advance,offset,Region.eval,Exp.eval,
      sub_eq_add_neg]

end GridGraphs.ResidueTwoLower.Poly
