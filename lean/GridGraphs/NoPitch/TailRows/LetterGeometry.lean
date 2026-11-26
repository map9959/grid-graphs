import GridGraphs.NoPitch.TailRows.LineTransport
import GridGraphs.NoPitch.Budget.LetterRows19

namespace GridGraphs.NoPitch.TailRows
open PitchCut Keys Budget Finset LocalBoard19
variable {k : Nat}

def center (r j : J k) : Site k := (teeth k r,teeth k j)
def turn (g : Fin 8) (x : Site k) := small (N k) g x

theorem turn_values (g : Fin 8) (x : Site k) :
    ((turn g x).1.val,(turn g x).2.val)=transform g (N k) x.1.val x.2.val := by
  have a := x.1.isLt; have b := x.2.isLt; unfold N at a b
  fin_cases g <;> norm_num [turn,small,transform,Fin.ofNat,N] <;>
    (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;> omega

theorem turn_inv (g : Fin 8) (x : Site k) : turn (invers g) (turn g x)=x := by
  have a := x.1.isLt; have b := x.2.isLt; unfold N at a b
  fin_cases g <;> norm_num [turn,small,invers,transform,Fin.ofNat,N,Prod.ext_iff,Fin.ext_iff] <;>
    (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;> omega

def turnEquiv (g : Fin 8) : Site k ≃ Site k :=
  ⟨turn g,turn (invers g),turn_inv g,fun x => by
    have h : invers (invers g)=g := by revert g; decide +kernel
    simpa only [h] using turn_inv (invers g) x⟩

theorem turnMem (F : Finset (Site k)) (g : Fin 8) (x : Site k) :
    turn g x∈view F g ↔ x∈F := by
  constructor
  · intro m; obtain ⟨y,hy,e⟩ := mem_image.mp m
    exact (turnEquiv g).injective e ▸ hy
  · exact mem_image_of_mem _

private def dr (d : Nat) : Int := if d=1 then 1 else if d=3 then -1 else 0
private def dc (d : Nat) : Int := if d=0 then 1 else if d=2 then -1 else 0
private theorem probe_iff (x y : Site k) (d : Fin 4) :
    probe x d.val=some y ↔ (y.1.val:Int)=x.1.val+dr d.val ∧ (y.2.val:Int)=x.2.val+dc d.val := by
  unfold probe; simp only [Option.dite_none_right_eq_some,Option.some.injEq]
  constructor
  · rintro ⟨h,rfl⟩; simp only [dr,dc,Int.toNat_of_nonneg h.1,Int.toNat_of_nonneg h.2.1,and_self]
  · rintro ⟨a,b⟩; unfold dr at a; unfold dc at b
    refine ⟨by simp only [←a,←b,Int.natCast_nonneg,Int.toNat_natCast,Fin.is_lt,and_self],?_⟩
    apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega

theorem turnProbe (g : Fin 8) (d : Fin 4) (x y : Site k) :
    probe (turn g x) (direction g d)=some (turn g y) ↔ probe x d.val=some y := by
  have m : direction g d.val<4 := by unfold direction; omega
  rw [probe_iff (turn g x) (turn g y) ⟨_,m⟩,probe_iff]
  have c (p : Site k) := turn_values g p
  have bounds (p : Site k) : p.1.val≤3*k ∧ p.2.val≤3*k := by
    have := p.1.isLt; have := p.2.isLt; unfold N at *; omega
  have cx := c x; have cy := c y; have := bounds x; have := bounds y
  fin_cases g <;> fin_cases d <;>
    norm_num [dr,dc,transform,direction,N,Prod.ext_iff] at cx cy ⊢ <;> omega

theorem turnBit (F : Finset (Site k)) (g : Fin 8) (x : Site k) (d : Fin 4) :
    bitsAt (view F g) (turn g x) (Fin.ofNat 4 (direction g d))=bitsAt F x d := by
  have v : (Fin.ofNat 4 (direction g d)).val=direction g d := Nat.mod_eq_of_lt (by unfold direction; omega)
  unfold bitsAt; rw [v]
  cases h : probe x d.val with
  | none =>
    cases p : probe (turn g x) (direction g d) with
    | none => rfl
    | some y =>
      obtain ⟨z,rfl⟩ := (turnEquiv g).surjective y
      have q := (turnProbe g d x z).mp p; rw [h] at q; contradiction
  | some y => rw [(turnProbe g d x y).mpr h]; simp only [Option.any_some,turnMem]

private theorem hor {F : Finset (Site k)} (r j : J k) :
    L F r j=⟨bitsAt F (center r j) 2,decide (center r j∈F),bitsAt F (center r j) 0⟩ := by
  have a : (teeth k r).val=3*r.val := rfl
  have b : (teeth k j).val=3*j.val := rfl
  have hr := (teeth k r).isLt; have hc := (teeth k j).isLt
  rw [a] at hr; rw [b] at hc
  unfold L letter; congr 1
  · by_cases l : 0<j.val
    · have bd : 3*j.val-1<N k := by omega
      let y : Site k := (teeth k r,⟨3*j.val-1,bd⟩)
      have e : probe (center r j) 2=some y := (probe_iff _ _ 2).mpr (by
        change ((teeth k r).val:Int)=((teeth k r).val:Int)+0 ∧ ((3*j.val-1:Nat):Int)=((3*j.val:Nat):Int)+(-1); omega)
      change probe (center r j) (2:Fin 4).val=some y at e
      simp only [decide_eq_true l,Bool.true_and,bit,dif_pos bd,bitsAt,e,Option.any_some]; rfl
    · have e : probe (center r j) 2=none := by
        cases h : probe (center r j) 2 with
        | none => rfl
        | some y =>
          have z := ((probe_iff _ _ 2).mp h).2
          change (y.2.val:Int)=((3*j.val:Nat):Int)+(-1) at z; omega
      simp [l,bitsAt,e]
  · simp only [bit,dif_pos hc]; rfl
  · by_cases bd : 3*j.val+1<N k
    · let y : Site k := (teeth k r,⟨3*j.val+1,bd⟩)
      have e : probe (center r j) 0=some y := (probe_iff _ _ 0).mpr (by
        change ((teeth k r).val:Int)=((teeth k r).val:Int)+0 ∧ ((3*j.val+1:Nat):Int)=((3*j.val:Nat):Int)+1; omega)
      change probe (center r j) (0:Fin 4).val=some y at e
      simp only [bit,dif_pos bd,bitsAt,e,Option.any_some]; rfl
    · have e : probe (center r j) 0=none := by
        cases h : probe (center r j) 0 with
        | none => rfl
        | some y =>
          have z := ((probe_iff _ _ 0).mp h).2; have := y.2.isLt
          change (y.2.val:Int)=((3*j.val:Nat):Int)+1 at z; omega
      simp [bit,bd,bitsAt,e]

theorem read_letter (F : Finset (Site k)) (g : Fin 8) (r j : J k) :
    let x := (turnEquiv g).symm (center r j)
    rotatedLetter g (decide (x∈F)) (bitsAt F x)=L (view F g) r j := by
  let x := (turnEquiv g).symm (center r j)
  have e : turn g x=center r j := (turnEquiv g).apply_symm_apply _
  have bits (d : Fin 4) : bitsAt F x (Fin.ofNat 4 (direction (invers g) d))=
      bitsAt (view F g) (center r j) d := by
    have inv : ∀ (g : Fin 8) (d : Fin 4), Fin.ofNat 4 (direction g (Fin.ofNat 4 (direction (invers g) d)).val)=d := by decide +kernel
    simpa only [inv,e] using (turnBit F g x (Fin.ofNat 4 (direction (invers g) d))).symm
  have m := turnMem F g x; rw [e] at m
  rw [hor]
  change rotatedLetter g (decide (x∈F)) (bitsAt F x)=_
  unfold rotatedLetter
  congr 1
  · exact bits 2
  · simp only [m]
  · exact bits 0

def atView {V : Type} [Zero V] (A : Nat → Nat → Letter → V) (x : Site k) (g : Fin 8)
    (f : Bool) (bits : Fin 4 → Bool) : V :=
  let y := turn g x
  if y.1.val%3=0 ∧ y.2.val%3=0 then
    A (axis (N k) 8 y.1.val) (axis (N k) 8 y.2.val) (rotatedLetter g f bits) else 0

theorem letter_frequencies (F : Finset (Site k)) (g : Fin 8) (A : Nat → Nat → Letter → Int) :
    (∑ x, atView A x g (decide (x∈F)) (bitsAt F x))=
      ∑ r : J k, ∑ j : J k, A (band k r) (band k j) (L (view F g) r j) := by
  let e (p : J k × J k) := (turnEquiv g).symm (center p.1 p.2)
  let f (x : Site k) := atView A x g (decide (x∈F)) (bitsAt F x)
  have inj : Function.Injective e := by
    intro p q h
    have z := (turnEquiv g).symm.injective h
    exact Prod.ext ((teeth k).injective (congrArg Prod.fst z)) ((teeth k).injective (congrArg Prod.snd z))
  have sub : ∑ x, f x=∑ x∈univ.image e, f x := by
    symm; apply sum_subset (subset_univ _); intro x _ absent
    unfold f atView; dsimp only; split <;> rename_i h
    · let y := turn g x
      have axisEq (z : Fin (N k)) (hz : z.val%3=0) : teeth k (owner z)=z := by
        apply Fin.ext; change 3*((z.val+1)/3)=z.val; omega
      have e₁ : center (owner y.1) (owner y.2)=y := Prod.ext (axisEq _ h.1) (axisEq _ h.2)
      apply False.elim; apply absent; apply mem_image.mpr
      refine ⟨(owner y.1,owner y.2),mem_univ _,?_⟩
      unfold e; rw [e₁]; exact (turnEquiv g).symm_apply_apply x
    · rfl
  change ∑ x, f x=_
  rw [sub,sum_image inj.injOn,Fintype.sum_prod_type]
  apply sum_congr rfl; intro r _
  apply sum_congr rfl; intro j _
  have y : turn g (e (r,j))=center r j := (turnEquiv g).apply_symm_apply _
  have t (u : J k) : (teeth k u).val=3*u.val := rfl
  simp only [f,atView,y,center,t,Nat.mul_mod_right,if_true,and_self]
  rw [show rotatedLetter g (decide (e (r,j)∈F)) (bitsAt F (e (r,j)))=_ from read_letter F g r j]; rfl

end GridGraphs.NoPitch.TailRows
