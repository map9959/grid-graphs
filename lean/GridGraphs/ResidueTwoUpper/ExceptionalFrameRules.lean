import GridGraphs.ResidueTwoUpper.ExceptionalReduction

/-! The 648 ranked messages for the physical boundary. Fine tags are
the actual period-three location coordinates; each spatial predicate uses
only distances zero, one, two, or at least three from each wall. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.Frame
open ResidueZero Stencil

def msgs : Std.HashMap Nat Nat := .ofList <|
  ((include_str "Data/frame.msg").splitOn "\n").filterMap fun s =>
    match s.splitOn " " with
    | [a,b] => do return (←a.toNat?,←b.toNat?)
    | _ => none
def rank (b : Bool) (k : Nat) := msgs.getD (2*k+b.toNat) 0
def starRank (n : Int) (p : Pos) (f nb : Nat) (b : Bool) (q : Fin 9) :=
  if inside (n-2) (p-offset q) then rank b (event n (p-offset q) p q (localEvent q f nb)) else 0
def patchRank (n : Int) (p : Pos) (m : Nat) (b : Bool) (q : Fin 9) :=
  rank b (event n p (p+offset q) q (localEvent q (bit m q) (patchNbr m q)))

def ends (last : Int) (r c : Int) := (r=0 ∨ r=last) ∧ (c=0 ∨ c=last)
instance (l r c : Int) : Decidable (ends l r c) := by unfold ends; infer_instance
def depth (last x : Int) := min x (last-x)
def starGood (r c : Int) (f nb o : Nat) (w : Int) : Bool := decide <|
  let a := depth 14 r; let b := depth 14 c
  let d := min a b
  let inward := ¬ends 14 r c ∧ ((r=0 ∧ o=1) ∨ (r=14 ∧ o=3) ∨ (c=0 ∧ o=0) ∨ (c=14 ∧ o=2))
  (d=0 ∧ 3 ≤ max a b → f=1) ∧ (d=1 → f=0) ∧
  (d=0 → (w=full ↔ inward)) ∧ (d≠0 ∧ w=full → d=2 ∧ f=0 ∧ nb=0 ∧ o=4)

def word (r c : Int) (m : Nat) :=
  let sample (i j : Nat) := bit m (3*(if r=0 then i else 2-i)+(if c=0 then j else 2-j))
  8*sample 0 1 + 4*sample 0 2 + 2*sample 1 0 + sample 2 0
def patchGood (r c : Int) (m : Nat) (w : Int) : Bool := decide <|
  (w=full → depth 12 r>0 ∧ depth 12 c>0) ∧
  (ends 12 r c → word r c m ∈ [3,7,12,13])

def S (n : Int) (p : Pos) (f nb o : Nat) := starGood (axis n 6 p.1) (axis n 6 p.2) f nb o
  (twoOrbitStar n p f nb o)
def W (n : Int) (a : Pos) (m : Nat) := patchGood (axis (n-2) 5 a.1) (axis (n-2) 5 a.2) m
  (twoOrbitPatch n a m)

def baseS := decide (∀ (i j : Fin 23) (f : Fin 2) (nb : Fin 16) (o : Fin 5),
  let p : Pos := (i.val,j.val)
  starOK 23 p f nb o → (ends 14 (axis 23 6 p.1) (axis 23 6 p.2) → f.val=1) →
  let w := twoOrbitStar 23 p f nb o
  w=0 ∨ w=full → traceOK (starRank 23 p f nb false) (starRank 23 p f nb true)
    (starGood (axis 23 6 p.1) (axis 23 6 p.2) f nb o w))
def baseP := decide (∀ (i j : Fin 21) (m : Fin 512),
  let p : Pos := (i.val,j.val)
  maskOK m → let w := twoOrbitPatch 23 p m
  w=0 ∨ w=full → traceOK (patchRank 23 p m true) (patchRank 23 p m false)
    (patchGood (axis 21 5 p.1) (axis 21 5 p.2) m w))

end GridGraphs.ResidueTwoUpper.Exceptional.Frame
