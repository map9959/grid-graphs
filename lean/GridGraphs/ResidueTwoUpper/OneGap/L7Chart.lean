import GridGraphs.ResidueTwoUpper.OneGap.PatchFilter
import GridGraphs.ResidueTwoUpper.OneGap.L7Scan
import GridGraphs.ResidueTwoUpper.TwoGapWords

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7
open ResidueZero Stencil

structure View where
  rowFar : Bool
  colFar : Bool
  swap : Bool
deriving DecidableEq, Fintype
def reflect (far : Bool) (n i : Int) := if far then n-1-i else i
def view (v : View) (n r j : Int) : Pos :=
  let p := if v.swap then (j,r) else (r,j)
  (reflect v.rowFar n p.1, reflect v.colFar n p.2)
def turnView (v : View) : View := {v with swap := !v.swap}
theorem turned (v : View) (n r j : Int) : view (turnView v) n r j=view v n j r := by
  cases v with | mk a b s => cases s <;> rfl

def encode (m : Fin 512) (v : View) : Nat :=
  ((List.finRange 9).map fun q =>
    let p := view v 3 (q.val/3:Nat) (q.val%3:Nat)
    bit m (posIdx p) <<< q.val).sum

def catTest (v : View) (r j : Nat) (m : Fin 512) : Bool :=
  let a := view v 33 r j
  let p := a+(1,1)
  !maskOK m || allowed r j (encode m v) ||
    (!(twoOrbitPatch 35 a m==0 || twoOrbitPatch 35 a m==full)) ||
    (List.range 5).all fun o =>
      !starOK 35 p (bit m 4) (PatchFilter.cnb m) o ||
      twoOrbitStar 35 p (bit m 4) (PatchFilter.cnb m) o != 0

def catCheck := decide (∀ v : View, ∀ r : Fin 5, ∀ j : Fin 33, ∀ m : Fin 512, catTest v r j m)

theorem inside_view {n r j : Nat} (v : View) (hr : r<n) (hj : j<n) :
    inside n (view v n r j) := by
  cases v with | mk a b s =>
    cases s <;> cases a <;> cases b <;> simp [view,reflect,inside] <;> omega

theorem view_center (v : View) (n r j : Int) :
    view v (n-2) r j+(1,1)=view v n (r+1) (j+1) := by
  cases v with | mk a b s =>
    cases s <;> cases a <;> cases b <;> ext <;> simp [view,reflect] <;> ring

set_option maxHeartbeats 2500000 in
private theorem transportAxis (u j : Nat) (d : Int) (hd : d=0 ∨ d=2) (t : Int)
    (ht : t=0 ∨ t=1) (far : Bool) :
    rep (23-d) (4+14*(u:Int)) (reflect far (35+42*(u:Int)-d) ((j:Int)+t)) =
      rep (23-d) 4 (reflect far (35-d) ((fold u j:Int)+t)) := by
  unfold reflect fold rep; rcases hd with rfl|rfl <;> rcases ht with rfl|rfl <;>
    cases far <;> split_ifs <;> push_cast <;> omega

private theorem chart (v : View) (u r j : Nat) (hr : r<5) (d t : Int)
    (hd : d=0 ∨ d=2) (ht : t=0 ∨ t=1) :
    representative (23-d) (4+14*(u:Int)) (view v (35+42*(u:Int)-d) (r+t) (j+t)) =
      representative (23-d) 4 (view v (35-d) (r+t) ((fold u j:Int)+t)) := by
  have A (far) := transportAxis u j d hd t ht far
  have B (far) := transportAxis u r d hd t ht far
  rw [show fold u r=r by simp [fold,show r<21 by omega]] at B
  cases v with | mk a b s =>
    cases s <;> apply Prod.ext <;> first | exact A _ | exact B _

theorem samePatch (v : View) (u r j : Nat) (hr : r<5) (m : Nat) :
    twoOrbitPatch (35+42*(u:Int)) (view v (33+42*(u:Int)) r j) m =
    twoOrbitPatch 35 (view v 33 r (fold u j)) m := by
  have eq : 35+42*(u:Int)-2=21+3*(4+14*(u:Int)) := by ring
  have A := patchLocation_transport (b:=21) (by decide) (j:=4+14*(u:Int)) (by positivity)
    (view v (33+42*(u:Int)) r j)
  have B := patchLocation_transport (b:=21) (by decide) (j:=4) (by decide)
    (view v 33 r (fold u j))
  have ch := chart v u r j hr 2 0 (.inr rfl) (.inl rfl)
  norm_num at B ch
  rw [show 35+42*(u:Int)-2=33+42*(u:Int) by ring] at ch
  simp only [twoOrbitPatch,eq,A,ch,B,show (35:Int)-2=33 by decide]

theorem sameStar (v : View) (u r j : Nat) (hr : r<5) (f b o : Nat) :
    twoOrbitStar (35+42*(u:Int)) (view v (35+42*(u:Int)) ((r:Int)+1) ((j:Int)+1)) f b o =
    twoOrbitStar 35 (view v 35 ((r:Int)+1) ((fold u j:Int)+1)) f b o := by
  have eq : 35+42*(u:Int)=23+3*(4+14*(u:Int)) := by ring
  have A := starLocation_transport (b:=23) (by decide) (j:=4+14*(u:Int)) (by positivity)
    (view v (35+42*(u:Int)) ((r:Int)+1) ((j:Int)+1))
  have B := starLocation_transport (b:=23) (by decide) (j:=4) (by decide)
    (view v 35 ((r:Int)+1) ((fold u j:Int)+1))
  have ch := chart v u r j hr 0 1 (.inl rfl) (.inr rfl)
  norm_num at ch B
  let p := view v (35+42*(u:Int)) ((r:Int)+1) ((j:Int)+1)
  let z := view v 35 ((r:Int)+1) ((fold u j:Int)+1)
  have loc (g : Nat) : starLocation (35+42*(u:Int)) (image (35+42*(u:Int)) g p) =
      starLocation 35 (image 35 g z) := by
    rw [eq,starLocation_transport (by decide : (19:Int)≤23) (by positivity),B]
    exact congrArg (fun q => starLocation 23 (image 23 g q)) ch
  change twoOrbitStar _ p _ _ _=twoOrbitStar _ z _ _ _
  simp only [twoOrbitStar,loc]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.L7
