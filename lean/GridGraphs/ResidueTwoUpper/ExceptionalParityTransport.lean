import GridGraphs.ResidueTwoUpper.ExceptionalParity

namespace GridGraphs.ResidueTwoUpper.Exceptional.Parity
open ResidueZero Stencil Finset

def reduce (b u i : Int) :=
  if i<7 then i else if b+42*u-7 ≤ i then i-42*u else 7+(i-7)%6
def project (b u : Int) (p : Pos) : Pos := (reduce b u p.1, reduce b u p.2)

private theorem same_rep (b u i : Int) (hb : b=33 ∨ b=35) (hu : 0≤u) :
    rep (b-12) (4+14*u) i=rep (b-12) 4 (reduce b u i) := by
  unfold rep reduce; split_ifs <;> omega

private theorem rep_eq (b u : Int) (hb : b=33 ∨ b=35) (hu : 0≤u) (p : Pos) :
    representative (b-12) (4+14*u) p=representative (b-12) 4 (project b u p) :=
  Prod.ext (same_rep b u p.1 hb hu) (same_rep b u p.2 hb hu)

private theorem reduced_inside (b u : Int) (hb : b=33 ∨ b=35) (_hu : 0≤u) (p : Pos)
    (hp : inside (b+42*u) p) : inside b (project b u p) := by
  simp [inside,project,reduce] at hp ⊢; split_ifs <;> omega

private theorem coord_rule (b u i δ t : Int) (hb : b=33 ∨ b=35) (hu : 0≤u)
    (h : δ=0 ∧ -1≤t ∧ t≤1 ∨ δ= -2 ∧ -2≤t ∧ t≤0) :
    ax (b+42*u+δ) (i+t)=ax (b+δ) (reduce b u i+t) ∧
      (0 ≤ i+t ∧ i+t<b+42*u+δ ↔ 0 ≤ reduce b u i+t ∧ reduce b u i+t<b+δ) := by
  unfold ax reduce; split_ifs <;> omega

private theorem query (b u : Int) (hb : b=33 ∨ b=35) (hu : 0≤u) (p t : Pos) (δ : Int)
    (h : δ=0 ∧ -1≤t.1 ∧ t.1≤1 ∧ -1≤t.2 ∧ t.2≤1 ∨
      δ= -2 ∧ -2≤t.1 ∧ t.1≤0 ∧ -2≤t.2 ∧ t.2≤0) :
    bucket (b+42*u+δ) (p+t)=bucket (b+δ) (project b u p+t) ∧
    inside (b+42*u+δ) (p+t)=inside (b+δ) (project b u p+t) := by
  have x := coord_rule b u p.1 δ t.1 hb hu (by tauto)
  have y := coord_rule b u p.2 δ t.2 hb hu (by tauto)
  constructor
  · simp [bucket,project,x.1,y.1]
  · apply Bool.eq_iff_iff.mpr
    simp only [inside,Bool.and_eq_true,decide_eq_true_eq]
    change (((0 ≤ p.1+t.1 ∧ p.1+t.1<_) ∧ 0 ≤ p.2+t.2) ∧ p.2+t.2<_) ↔
      (((0 ≤ reduce b u p.1+t.1 ∧ reduce b u p.1+t.1<_) ∧ 0 ≤ reduce b u p.2+t.2) ∧ reduce b u p.2+t.2<_)
    constructor
    · rintro ⟨⟨a,b'⟩,c⟩
      have r := x.2.mp a; have s := y.2.mp ⟨b',c⟩
      exact ⟨⟨r,s.1⟩,s.2⟩
    · rintro ⟨⟨a,b'⟩,c⟩
      have r := x.2.mpr a; have s := y.2.mpr ⟨b',c⟩
      exact ⟨⟨r,s.1⟩,s.2⟩

private theorem shifted (p : Pos) (d : Nat) : shift p d=p+shift (0,0) d := by
  unfold shift; split <;> ext <;> simp [sub_eq_add_neg]
private theorem shiftQuery (b u : Int) (hb : b=33 ∨ b=35) (hu : 0≤u) (p : Pos) (d : Nat) :
    bucket (b+42*u) (shift p d)=bucket b (shift (project b u p) d) ∧
    inside (b+42*u) (shift p d)=inside b (shift (project b u p) d) := by
  have h : -1≤(shift (0,0) d).1 ∧ (shift (0,0) d).1≤1 ∧
      -1≤(shift (0,0) d).2 ∧ (shift (0,0) d).2≤1 := by unfold shift; split <;> decide
  simpa only [add_zero,←shifted] using query b u hb hu p (shift (0,0) d) 0 (.inl ⟨rfl,h⟩)

private theorem center (b u : Int) (hb : b=33 ∨ b=35) (hu : 0≤u) (p : Pos) :
    bucket (b+42*u) p=bucket b (project b u p) := by
  simpa using (query b u hb hu p 0 0 (.inl (by decide))).1

private theorem bond_transport (b u : Int) (hb : b=33 ∨ b=35) (hu : 0≤u) (p : Pos) (k d ev) :
    bond k (b+42*u) p d ev=bond k b (project b u p) d ev := by
  simp only [bond,(shiftQuery b u hb hu p d).1,(shiftQuery b u hb hu p d).2,center b u hb hu p]

private theorem cover_transport (u : Int) (hu : 0≤u) (p : Pos) (f nb) (q : Fin 9) :
    cover (35+42*u) p f nb q=cover 35 (project 35 u p) f nb q := by
  have h : -2≤(-(offset q)).1 ∧ (-(offset q)).1≤0 ∧ -2≤(-(offset q)).2 ∧ (-(offset q)).2≤0 := by
    have := q.isLt; simp [offset]; omega
  have z := query 35 u (.inr rfl) hu p (-offset q) (-2) (.inr ⟨rfl,h⟩)
  simp only [cover,sub_eq_add_neg,z.1,z.2]

private theorem charges_star (u : Nat) (p : Pos) (f nb o) :
    twoOrbitStar (35+42*(u:Int)) p f nb o=twoOrbitStar 35 (project 35 u p) f nb o := by
  have e : 35+42*(u:Int)=23+3*(4+14*(u:Int)) := by ring
  have A := starLocation_transport (b:=23) (by decide) (j:=4+14*(u:Int)) (by positivity) p
  have B := starLocation_transport (b:=23) (by decide) (j:=4) (by decide) (project 35 u p)
  norm_num1 at B
  have eq := rep_eq 35 u (.inr rfl) (by positivity) p
  change representative 23 _ p=representative 23 4 _ at eq
  simp only [twoOrbitStar,e,A,eq,B]

private theorem charges_patch (u : Nat) (p : Pos) (m) :
    twoOrbitPatch (35+42*(u:Int)) p m=twoOrbitPatch 35 (project 33 u p) m := by
  have e : 35+42*(u:Int)-2=21+3*(4+14*(u:Int)) := by ring
  have A := patchLocation_transport (b:=21) (by decide) (j:=4+14*(u:Int)) (by positivity) p
  have B := patchLocation_transport (b:=21) (by decide) (j:=4) (by decide) (project 33 u p)
  norm_num1 at B
  have eq := rep_eq 33 u (.inl rfl) (by positivity) p
  change representative 21 _ p=representative 21 4 _ at eq
  simp only [twoOrbitPatch,e,A,eq,show (35:Int)-2=33 by decide,B]

private theorem root_transport (u : Nat) (p : Pos) (o) :
    rootOK (35+42*(u:Int)) p o=rootOK 35 (project 35 u p) o := by
  have pair (i : Int) : (i=0 ↔ reduce 35 u i=0) ∧
      (i=35+42*(u:Int)-1 ↔ reduce 35 u i=35-1) := by unfold reduce; split_ifs <;> omega
  simp only [rootOK,Prod.ext_iff,project,(pair p.1).1,(pair p.1).2,(pair p.2).1,(pair p.2).2]
  rfl

private theorem asFin (b : Nat) (p : Pos) (h : inside b p) :
    ∃ i j : Fin b, ((i.val:Int),(j.val:Int))=p := by
  simp [inside] at h
  exact ⟨⟨_,show p.1.toNat<b by omega⟩,⟨_,show p.2.toNat<b by omega⟩,
    Prod.ext (by dsimp; omega) (by dsimp; omega)⟩

theorem star_even (checked : starCheck) (u : Nat) (p : Pos) (hp : inside (35+42*(u:Int)) p)
    (f : Fin 2) (nb : Fin 16) (o : Fin 5) (ok : starOK (35+42*(u:Int)) p f nb o)
    (rt : rootOK (35+42*(u:Int)) p o)
    (w : twoOrbitStar (35+42*(u:Int)) p f nb o=0 ∨ twoOrbitStar (35+42*(u:Int)) p f nb o=half) :
    starBill (35+42*(u:Int)) p f nb o %2=0 := by
  have cv := cover_transport (u:Int) (by positivity) p f nb
  have bd := bond_transport 35 u (.inr rfl) (by positivity) p 2
  simp only [starBill,port,bd,cv]
  have loc := reduced_inside 35 u (.inr rfl) (by positivity) p hp
  have same (d) := (shiftQuery 35 u (.inr rfl) (by positivity) p d).2
  simp only [starOK,same] at ok
  rw [root_transport] at rt; simp only [charges_star] at w
  obtain ⟨i,j,e⟩ := asFin 35 _ loc
  have cert := of_decide_eq_true checked i j f nb o
  rw [e] at cert
  exact cert ok rt w

theorem patch_even (checked : patchCheck) (u : Nat) (p : Pos) (hp : inside (33+42*(u:Int)) p)
    (m : Fin 512) (ok : maskOK m)
    (w : twoOrbitPatch (35+42*(u:Int)) p m=0 ∨ twoOrbitPatch (35+42*(u:Int)) p m=half) :
    patchBill (35+42*(u:Int)) p m%2=0 := by
  have bd := bond_transport 33 u (.inl rfl) (by positivity) p 3
  have cen := center 33 u (.inl rfl) (by positivity) p
  simp only [patchBill,strip,slot,special,show 35+42*(u:Int)-2=33+42*u by ring,bd,cen]
  have loc := reduced_inside 33 u (.inl rfl) (by positivity) p hp
  simp only [charges_patch] at w
  obtain ⟨i,j,e⟩ := asFin 33 _ loc
  have cert := of_decide_eq_true checked i j m
  rw [e] at cert
  exact cert ok w

end GridGraphs.ResidueTwoUpper.Exceptional.Parity
