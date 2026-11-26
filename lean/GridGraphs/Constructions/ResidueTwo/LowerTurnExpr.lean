import GridGraphs.Constructions.ResidueTwo.LowerTurnCheck

namespace GridGraphs.ResidueTwoLower.Poly

inductive Exp
  | t | i | j | lit (x : ℤ)
  | add (a b : Exp) | mul (k : ℤ) (a : Exp)
  | div (a : Exp) (k : ℤ) | mod (a : Exp) (k : ℤ)
  deriving Inhabited, Repr

def Exp.eval (t i j : ℤ) : Exp → ℤ
  | .t => t | .i => i | .j => j | .lit x => x
  | .add a b => a.eval t i j+b.eval t i j | .mul k a => k*a.eval t i j
  | .div a k => a.eval t i j/k | .mod a k => a.eval t i j%k

/- An affine substitution for a fixed triple of parameter and site residues. -/
structure Sub where
  t : Lin
  i : Lin
  j : Lin
  deriving Inhabited

def Exp.lower (s : Sub) : Exp → Option Lin
  | .t => some s.t | .i => some s.i | .j => some s.j | .lit x => some ⟨0,0,0,x⟩
  | .add a b => return (← a.lower s).add (← b.lower s)
  | .mul k a => return (← a.lower s).mul k
  | .div a k => do
    let x ← a.lower s
    guard (0<k && x.divides k)
    return x.den k
  | .mod a k => do
    let x ← a.lower s
    guard (0<k && x.divides k)
    return ⟨0,0,0,x.d%k⟩

theorem Exp.lower_sound (e : Exp) (s : Sub) (t i j) {v} (h : e.lower s=some v) :
    v.val t i j = e.eval (s.t.val t i j) (s.i.val t i j) (s.j.val t i j) := by
  induction e generalizing v <;> simp only [lower,eval] at *
  case t | i | j => simpa using congrArg (fun x => (x.getD default).val t i j) h.symm
  case lit x => obtain rfl := Option.some.inj h; simp [Lin.val]
  case add a b ha hb =>
    cases sa : a.lower s <;> simp [sa] at h
    cases sb : b.lower s <;> simp [sb] at h
    subst v; simp [ha sa,hb sb]
  case mul k a ha =>
    cases sa : a.lower s <;> simp [sa] at h
    subst v; simp [ha sa]
  case div a k ha =>
    cases sa : a.lower s with
    | none => simp [sa] at h
    | some x =>
      by_cases g : 0<k ∧ x.divides k=true
      · simp [sa,guard,g.1,g.2] at h; subst v
        rw [Lin.den_val _ _ _ _ _ g.1 g.2,ha sa]
      · simp [sa,guard,g] at h
  case mod a k ha =>
    cases sa : a.lower s with
    | none => simp [sa] at h
    | some x =>
      by_cases g : 0<k ∧ x.divides k=true
      · simp [sa,guard,g.1,g.2] at h; subst v
        have hd := Lin.den_val x k t i j g.1 g.2
        rw [←ha sa]; simp [Lin.val] at *
        have dv := g.2
        simp [Lin.divides] at dv
        obtain ⟨⟨xt,xi⟩,xj⟩ := dv
        have d : k ∣ x.t*t+x.i*i+x.j*j := dvd_add (dvd_add (dvd_mul_of_dvd_left xt _)
          (dvd_mul_of_dvd_left xi _)) (dvd_mul_of_dvd_left xj _)
        rw [Int.add_emod,Int.emod_eq_zero_of_dvd d,zero_add,Int.emod_emod]
      · simp [sa,guard,g] at h

inductive Region
  | yes | no | ge (a b : Exp) | both (p q : Region) | either (p q : Region)
  deriving Inhabited

def Region.eval (t i j : ℤ) : Region → Prop
  | .yes => True | .no => False | .ge a b => b.eval t i j ≤ a.eval t i j
  | .both p q => p.eval t i j ∧ q.eval t i j | .either p q => p.eval t i j ∨ q.eval t i j

def Region.lower (s : Sub) : Region → Option Formula
  | .yes => some .yes | .no => some .no
  | .ge a b => do
    let l := (←a.lower s).add ((←b.lower s).mul (-1))
    if l.t==0 && l.i==0 && l.j==0 then return if l.d≥0 then .yes else .no
    return .test l.norm
  | .both p q => return (←p.lower s).band (←q.lower s)
  | .either p q => return (←p.lower s).bor (←q.lower s)

theorem Region.lower_sound (p : Region) (s : Sub) (t i j) {v} (h : p.lower s=some v) :
    v.denote t i j ↔ p.eval (s.t.val t i j) (s.i.val t i j) (s.j.val t i j) := by
  induction p generalizing v <;> simp only [lower,eval] at *
  case yes | no => obtain rfl := Option.some.inj h; rfl
  case ge a b =>
    cases sa : a.lower s <;> simp [sa] at h
    cases sb : b.lower s <;> simp [sb] at h
    rename_i x
    rename_i y
    let z := y.add (x.mul (-1))
    have id : z.val t i j = a.eval (s.t.val t i j) (s.i.val t i j) (s.j.val t i j) -
        b.eval (s.t.val t i j) (s.i.val t i j) (s.j.val t i j) := by
      simp [z,Exp.lower_sound _ _ _ _ _ sa,Exp.lower_sound _ _ _ _ _ sb]; ring
    change (if (z.t=0 ∧ z.i=0) ∧ z.j=0 then some (if 0 ≤ z.d then .yes else .no)
      else some (.test z.norm))=some v at h
    split at h
    · rename_i g
      have eq : z.val t i j=z.d := by
        simp [Lin.val,g.1.1,g.1.2,g.2]
      rw [←sub_nonneg,←id,eq]
      by_cases pos : 0 ≤ z.d
      · simp only [if_pos pos,Option.some.injEq] at h
        subst v; simp [Formula.denote,pos]
      · simp only [if_neg pos,Option.some.injEq] at h
        subst v; simp [Formula.denote,pos]
    · obtain rfl := Option.some.inj h
      change 0 ≤ z.norm.val t i j ↔ _
      have hn : 0 ≤ z.norm.val t i j ↔ 0 ≤ z.val t i j := by
        unfold Lin.norm; dsimp only; split
        · rename_i g; simp at g
          rw [Lin.den_val _ _ _ _ _ (by omega) g.2]
          exact Int.ediv_nonneg_iff_of_pos (by omega)
        · rfl
      rw [hn,id]; omega
  case both a b ha hb | either a b ha hb =>
    cases sa : a.lower s <;> simp [sa] at h
    cases sb : b.lower s <;> simp [sb] at h
    subst v; simp [ha sa,hb sb]

end GridGraphs.ResidueTwoLower.Poly
