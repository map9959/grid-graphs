import GridGraphs.ResidueTwoUpper.Normalization

namespace GridGraphs.ResidueTwoUpper.Views
open Finset NoPitch.Keys Location GridGraphs.ResidueTwoUpper.Star

def mirrored (d a : Nat) := if d≤a ∧ a<d+3 then d+(7-(a-d))%3 else 2*d+2-a
theorem axis_mirror {d t i} (hi : i<2*d+8+3*t) :
    Location.axis (2*d+8+3*t) d (2*d+8+3*t-1-i) = mirrored d (Location.axis (2*d+8+3*t) d i) := by
  simp only [Location.axis,mirrored]; split_ifs <;> omega

def image (s : Nat) (g : Fin 8) (x : Site s) : Site s :=
  let rev (i : Fin s) : Fin s := ⟨s-1-i.val,by omega⟩
  let b := if g.val≥4 then rev x.2 else x.2
  match g.val%4 with
  | 0 => (x.1,b)
  | 1 => (b,rev x.1)
  | 2 => (rev x.1,rev b)
  | _ => (rev b,x.1)

theorem coordinates {s} (g : Fin 8) (x : Site s) :
    ((image s g x).1.val,(image s g x).2.val) = transform g s x.1 x.2 := by
  fin_cases g <;> rfl

private theorem inverse {s} (g : Fin 8) (x : Site s) :
    image s (invers g) (image s g x)=x := by
  have a := x.1.isLt; have b := x.2.isLt
  fin_cases g <;> apply Prod.ext <;> apply Fin.ext <;> simp [image,invers] <;> omega

def equiv (s : Nat) (g : Fin 8) : Site s ≃ Site s :=
  ⟨image s g,image s (invers g),inverse g,by
    have inv : invers (invers g)=g := by fin_cases g <;> rfl
    intro x; simpa [inv] using inverse (invers g) x⟩

def fine (s d : Nat) (p : Nat × Nat) := Location.axis s d p.1*16+Location.axis s d p.2
def turned (d a b : Nat) (g : Fin 8) :=
  let z := if g.val≥4 then mirrored d b else b
  let z' := if g.val≥4 then b else mirrored d b
  match g.val%4 with
  | 0 => a*16+z
  | 1 => z*16+mirrored d a
  | 2 => mirrored d a*16+z'
  | _ => z'*16+a

theorem fine_image {d t i j} (hi : i<2*d+8+3*t) (hj : j<2*d+8+3*t) (g : Fin 8) :
    let s := 2*d+8+3*t
    fine s d (transform g s i j)=turned d (Location.axis s d i) (Location.axis s d j) g := by
  dsimp only
  have rj : 2*d+8+3*t-1-(2*d+8+3*t-1-j)=j := by omega
  fin_cases g <;> dsimp [fine,transform,turned] <;>
    simp only [rj,axis_mirror hi,axis_mirror hj]

def units (d a b z : Nat) : Int := ∑ g : Fin 8, if turned d a b g=z then 1 else 0

theorem units_invariant {d a b : Nat} (da : d=5 ∨ d=6) (ha : a<2*d+3) (hb : b<2*d+3)
    (g : Fin 8) (z : Fin 256) :
    units d ((turned d a b g)/16) ((turned d a b g)%16) z = units d a b z := by
  have run (d : Nat) (hd : d=5 ∨ d=6) : ∀ (a b : Fin (2*d+3)) (g : Fin 8) (z : Fin 256),
      units d ((turned d a b g)/16) ((turned d a b g)%16) z = units d a b z := by
    rcases hd with rfl|rfl <;> native_decide
  exact run d da ⟨a,ha⟩ ⟨b,hb⟩ g z

theorem sum_units {d t} (hd : d=5 ∨ d=6) (a b : Fin 16) :
    let s := 2*d+8+3*t
    (∑ x : Site s, units d (Location.axis s d x.1) (Location.axis s d x.2) (a.val*16+b.val)) =
      8*Normalization.axisMass d t a*Normalization.axisMass d t b := by
  dsimp only; unfold units
  rw [sum_comm]
  have lim (i : Fin (2*d+8+3*t)) : Location.axis (2*d+8+3*t) d i <16 := by
    unfold Location.axis; have h := i.isLt; split_ifs <;> omega
  have sum1 (g : Fin 8) :
      (∑ x : Site (2*d+8+3*t), if turned d (Location.axis (2*d+8+3*t) d x.1) (Location.axis (2*d+8+3*t) d x.2) g=a.val*16+b.val
        then (1:Int) else 0) = Normalization.axisMass d t a*Normalization.axisMass d t b := by
    simp_rw [←fine_image (d:=d) (t:=t) (Fin.isLt _) (Fin.isLt _) g,←coordinates]
    let f (x : Site (2*d+8+3*t)) : Int := if Location.axis (2*d+8+3*t) d x.1=a ∧ Location.axis (2*d+8+3*t) d x.2=b then 1 else 0
    have eq (x : Site (2*d+8+3*t)) : (if fine (2*d+8+3*t) d (x.1.val,x.2.val)=a.val*16+b.val then (1:Int) else 0)=f x := by
      unfold f fine; dsimp only
      have ha := a.isLt; have hb := b.isLt; have l := lim x.2
      split_ifs <;> omega
    simp_rw [eq]
    exact ((equiv _ g).sum_comp f).trans (Normalization.count_locations hd t a b)
  simp [sum1,mul_assoc]

end GridGraphs.ResidueTwoUpper.Views
