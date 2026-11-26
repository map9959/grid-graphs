import GridGraphs.NoPitch.PhysicalKeys
import GridGraphs.NoPitch.SparseDual

namespace GridGraphs.NoPitch.TailRows
open Finset Keys GridGraphs.NoPitch.Dual

/-- A fibre is a collection of stride-three rows, with affine starting
column and affine row length. All arithmetic includes the width step. -/
structure Strip where
  x : Int
  dx : Int
  y : Int
  dy : Int
  sy : Int
  h : Int
  dh : Int
  w : Int
  dw : Int
  sw : Int
  deriving Inhabited, Repr
def Strip.height (s : Strip) (u : Nat) := s.h+s.dh*u
def Strip.width (s : Strip) (u i : Nat) := s.w+s.dw*u+s.sw*i
def Strip.X (s : Strip) (u i : Nat) := s.x+s.dx*u+3*i
def Strip.Y (s : Strip) (u i j : Nat) := s.y+s.dy*u+s.sy*i+3*j
def Strip.bounds (s : Strip) (n u : Nat) := ∀ i : Nat, (i:Int)<s.height u →
  0 ≤ s.width u i ∧ 0 ≤ s.X u i ∧ s.X u i<n ∧ ∀ j : Nat, (j:Int)<s.width u i → 0 ≤ s.Y u i j ∧ s.Y u i j<n
def Strip.fibre (s : Strip) (n h u : Nat) (pat : List Nat) :=
  ∀ x y : Nat, x<n → y<n →
    let i := (((x:Int)-s.x-s.dx*u)/3).toNat
    let j := (((y:Int)-s.y-s.dy*u-s.sy*i)/3).toNat
    fine n h x y=pat ↔ (i:Int)<s.height u ∧ (j:Int)<s.width u i ∧ (x:Int)=s.X u i ∧ (y:Int)=s.Y u i j

def Strip.size2 (s : Strip) (u : Nat) :=
  s.height u*(2*(s.w+s.dw*u)+s.sw*(s.height u-1))

theorem count_strip (s : Strip) (n h u : Nat) (pat : List Nat) (height : 0 ≤ s.height u)
    (bounds : s.bounds n u) (fibre : s.fibre n h u pat) :
    2*((univ.filter (fun p : Fin n × Fin n => fine n h p.1.val p.2.val=pat)).card:Int)=s.size2 u := by
  let H := (s.height u).toNat
  let W (i : Fin H) := (s.width u i).toNat
  have hi (i : Fin H) : (i.val:Int)<s.height u := by have := i.isLt; dsimp [H] at this; omega
  let e (p : (i : Fin H) × Fin (W i)) : Fin n × Fin n :=
    let b := bounds _ (hi p.1)
    let a := b.2.2.2 p.2.val (by have := p.2.isLt; dsimp [W] at this; omega)
    (⟨(s.X u p.1).toNat,by omega⟩,⟨(s.Y u p.1 p.2).toNat,by omega⟩)
  have vals (p : (i : Fin H) × Fin (W i)) :
      ((e p).1.val:Int)=s.X u p.1 ∧ ((e p).2.val:Int)=s.Y u p.1 p.2 := by
    have b := bounds _ (hi p.1)
    have a := b.2.2.2 p.2.val (by have := p.2.isLt; dsimp [W] at this; omega)
    exact ⟨Int.toNat_of_nonneg b.2.1,Int.toNat_of_nonneg a.1⟩
  have inj : Function.Injective e := by
    rintro ⟨i,j⟩ ⟨l,m⟩ eq
    have a := vals ⟨i,j⟩; have b := vals ⟨l,m⟩; rw [eq] at a
    have x := a.1.symm.trans b.1; dsimp [Strip.X] at x
    have z : i=l := Fin.ext (by omega)
    subst l; have y := a.2.symm.trans b.2; dsimp [Strip.Y] at y
    have z : j=m := Fin.ext (by omega); subst m; rfl
  have sets : (univ.filter (fun p : Fin n × Fin n => fine n h p.1.val p.2.val=pat))=univ.image e := by
    ext p; simp only [mem_filter,mem_univ,true_and,mem_image]
    have ff := fibre p.1.val p.2.val p.1.isLt p.2.isLt; dsimp only at ff; rw [ff]
    constructor
    · rintro ⟨iLt,jLt,x,y⟩
      let i : Fin H := ⟨(((p.1.val:Int)-s.x-s.dx*u)/3).toNat,by dsimp [H]; omega⟩
      let j : Fin (W i) := ⟨(((p.2.val:Int)-s.y-s.dy*u-s.sy*i.val)/3).toNat,by dsimp [W,i]; omega⟩
      refine ⟨⟨i,j⟩,Prod.ext (Fin.ext ?_) (Fin.ext ?_)⟩
      · exact_mod_cast (vals ⟨i,j⟩).1.trans x.symm
      · exact_mod_cast (vals ⟨i,j⟩).2.trans y.symm
    · rintro ⟨⟨i,j⟩,rfl⟩
      have v := vals ⟨i,j⟩
      rw [v.1,v.2]
      have id₁ : ((s.X u i-s.x-s.dx*u)/3).toNat=i.val := by unfold Strip.X; omega
      rw [id₁]
      have id₂ : ((s.Y u i j-s.y-s.dy*u-s.sy*i)/3).toNat=j.val := by unfold Strip.Y; omega
      rw [id₂]; exact ⟨hi i,by have := j.isLt; dsimp [W] at this; omega,rfl,rfl⟩
  rw [sets,card_image_of_injective _ inj,card_univ,Fintype.card_sigma]
  simp only [Fintype.card_fin,Nat.cast_sum]
  have wt (i : Fin H) : ((W i:Nat):Int)=s.width u i := Int.toNat_of_nonneg (bounds _ (hi i)).1
  simp only [wt,Strip.width,sum_add_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have sumI : 2*(∑ i : Fin H, (i.val:Int))=(H:Int)*(H-1:Int) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (i:Int)),←Nat.cast_sum]
    cases H with
    | zero => simp
    | succ t =>
      have h := sum_range_id_mul_two (t+1)
      rw [show ((t+1:Nat):Int)-1=(t:Int) by omega]
      exact_mod_cast (by simpa [mul_comm] using h : 2*(∑ i∈range (t+1),i)=(t+1)*t)
  have hH : (H:Int)=s.height u := Int.toNat_of_nonneg height
  unfold Strip.size2
  rw [←hH]; linear_combination s.sw*sumI

end GridGraphs.NoPitch.TailRows
