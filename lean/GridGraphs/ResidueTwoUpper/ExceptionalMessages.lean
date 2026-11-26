import GridGraphs.ResidueTwoUpper.ExceptionalBudget

/-! Ranked local inconsistency messages. A message concerns the *same*
physical star/patch incidence on both sides. Zero rank means no message;
a positive message can only be emitted by a cheap occurrence if it forces
an opposite-end message of strictly smaller positive rank. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional
open ResidueZero Stencil

def messages : Std.HashMap Nat Nat := .ofList <|
  ((include_str "Data/exceptional.msg").splitOn "\n").filterMap fun s =>
    match s.splitOn " " with
    | [a,b] => do return (←a.toNat?,←b.toNat?)
    | _ => none

def rank (patch : Bool) (code : Nat) := messages.getD (2*code+patch.toNat) 0
def event (n : Int) (a p : Pos) (q ev : Nat) := key (atPos (n-2) 4 a) (atPos n 5 p) q ev
def starRank (n : Int) (p : Pos) (f nb : Nat) (patch : Bool) (q : Fin 9) :=
  if inside (n-2) (p-offset q) then rank patch (event n (p-offset q) p q (localEvent q f nb)) else 0
def patchRank (n : Int) (a : Pos) (m : Nat) (patch : Bool) (q : Fin 9) :=
  rank patch (event n a (a+offset q) q (localEvent q (bit m q) (patchNbr m q)))

def traceOK (own other : Fin 9 → Nat) (good : Bool) : Prop :=
  (∀ q, own q ≠ 0 → ∃ r, 0<other r ∧ other r<own q) ∧
    (good=false → ∃ r, 0<other r)
instance (a b good) : Decidable (traceOK a b good) := by unfold traceOK; infer_instance

def half : Int := 1521000792
def threeQuarters : Int := 2281501188
def full : Int := 3042001584
def weights (w : Int) := w==0 || w==half || w==threeQuarters || w==full

def starRule (n : Int) (p : Pos) (f nb o : Nat) : Bool :=
  if !starOK n p f nb o then true else
  let w := twoOrbitStar n p f nb o
  if full<w then true else decide (traceOK (starRank n p f nb false) (starRank n p f nb true) (weights w))
def patchRule (n : Int) (p : Pos) (m : Nat) : Bool :=
  if !maskOK m then true else
  let w := twoOrbitPatch n p m
  if full<w then true else decide (traceOK (patchRank n p m true) (patchRank n p m false) (weights w))

def baseStars : Bool := decide (∀ i j : Fin 23, ∀ f : Fin 2, ∀ b : Fin 16, ∀ o : Fin 5,
  starRule 23 (i.val,j.val) f b o)
def basePatches : Bool := decide (∀ i j : Fin 21, ∀ m : Fin 512, patchRule 23 (i.val,j.val) m)

theorem checked_stars : baseStars := by native_decide
theorem checked_patches : basePatches := by native_decide

end GridGraphs.ResidueTwoUpper.Exceptional
