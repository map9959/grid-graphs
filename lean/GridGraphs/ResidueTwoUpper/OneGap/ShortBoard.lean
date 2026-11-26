import GridGraphs.ResidueTwoUpper.OneGap.ShortScan

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero Stencil L7 FanSlab

def center (r c : Nat) : Pos := (r+1,c+1)
def unview (w : View) (s : Nat) (r c : Nat) : Nat × Nat :=
  let a := if w.rowFar then s-1-r else r
  let b := if w.colFar then s-1-c else c
  if w.swap then (b,a) else (a,b)

def skin (n r c : Nat) : Option Bool :=
  let a := min r (n-1-r); let b := min c (n-1-c)
  if min a b=1 then some false else if min a b=0 ∧ 3 ≤ max a b then some true else none
def frameOK (n r c m : Nat) := (List.finRange 9).all fun (i : Fin 9) =>
  (skin n (r+i.val/3) (c+i.val%3)).all (fun b => bit m i==b.toNat)
def wall (n r c d : Nat) :=
  let t := shift (center r c) d
  Frame.depthAt n t==0
def wallOK (n r c m o : Nat) := (List.finRange 4).all fun (d : Fin 4) =>
  !wall n r c d || ((o==d.val)==decide (contact m d))

/-- The seed constraints are read in its own frame; prices and arrows
remain in the original frame. No covariance of a chosen parent is assumed. -/
def seedOK (n q : Nat) (w : View) (r c m : Nat) :=
  let (a,b) := unview w (n-2) r c
  if a=1 ∧ b%3=1 then
    if b<1+3*q then bit m 4==1
    else encode (Fin.ofNat 512 m) w == (if b=1+3*q then 64 else 72)
  else true

def starPrice (n r c : Nat) (f nb o : Nat) :=
  starOK n (center r c) f nb o && twoOrbitStar n (center r c) f nb o==0
def patchPrice (n r c m : Nat) := maskOK m && twoOrbitPatch n (r,c) m==0

/-- Cache the star table separately: a price only depends on the five
cross bits, whereas mask overlaps retain all nine. -/
@[noinline] def localDomain (n r c : Nat) : List Label :=
  let stars := Vector.ofFn fun (f : Fin 2) => Vector.ofFn fun (b : Fin 16) =>
    (List.range 5).filter fun o => starPrice n r c f b o
  ((List.range 512).filter fun m => frameOK n r c m && patchPrice n r c m).flatMap fun m =>
    ((stars[bit m 4 % 2][PatchFilter.cnb m % 16]).filter (wallOK n r c m)).map (m,·)
def localBoard (n : Nat) := build (n-2) (localDomain n)

@[noinline] def planted (n q : Nat) (w : View) (cache : Board) : Board :=
  build (n-2) fun r c =>
    if unview w (n-2) r c=(1,1+3*q) then
      ((List.range 512).filter (seedOK n q w r c)).map (·,4)
    else (atRC cache r c).filter fun z => seedOK n q w r c z.1

def dead (A : Board) := A.any (fun row => row.any List.isEmpty)
def emptyAt (A : Board) (s : Nat) :=
  (List.finRange s).any (fun (r : Fin s) => (List.finRange s).any fun (c : Fin s) => (atRC A r c).isEmpty)
def reject (s : Nat) (A : Board) (fuel : Nat) :=
  match fuel with
  | 0 => emptyAt A s
  | t+1 => emptyAt A s || reject s (round s A) t
termination_by fuel
theorem reject_sound {s A fuel M} (ok : reject s A fuel) (e : Agree s M) : ¬Kept s M A := by
  intro in'
  have live (A : Board) (h : Kept s M A) : ¬emptyAt A s := by
    intro gone
    obtain ⟨r,_,h'⟩ := List.any_eq_true.mp gone
    obtain ⟨c,_,z⟩ := List.any_eq_true.mp h'
    have mem := h r r.isLt c c.isLt
    rw [List.isEmpty_iff.mp z] at mem; contradiction
  induction fuel generalizing A with
  | zero => exact live A in' (by simpa [reject] using ok)
  | succ t ih =>
    rw [reject] at ok
    exact ih ((Bool.or_eq_true_iff.mp ok).resolve_left (live _ in')) (prune_kept in' e 1)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
