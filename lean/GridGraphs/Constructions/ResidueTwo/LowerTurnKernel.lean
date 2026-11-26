import Init

/-! Pure executable part of the zipper certificate checker. Keeping this module
free of proof-only dependencies allows compiling it as a small native plugin. -/
namespace GridGraphs.ResidueTwoLower.Poly

local notation "ℤ" => Int

structure Lin where
  t : ℤ
  i : ℤ
  j : ℤ
  d : ℤ
  deriving DecidableEq, Repr, Inhabited

def Lin.add (a b : Lin) : Lin := ⟨a.t+b.t,a.i+b.i,a.j+b.j,a.d+b.d⟩

def Lin.mul (k : ℤ) (a : Lin) : Lin := ⟨k*a.t,k*a.i,k*a.j,k*a.d⟩

def Lin.neg (a : Lin) : Lin := ⟨-a.t,-a.i,-a.j,-a.d-1⟩

def Lin.den (a : Lin) (k : ℤ) : Lin := ⟨a.t/k,a.i/k,a.j/k,a.d/k⟩

def Lin.divides (a : Lin) (k : ℤ) := a.t%k==0 && a.i%k==0 && a.j%k==0

def Lin.entails (a b : Lin) := a.t==b.t && a.i==b.i && a.j==b.j && a.d≤b.d

def Lin.norm (a : Lin) : Lin :=
  let k : ℤ := (a.t.gcd a.i).gcd a.j.natAbs
  if k>1 && a.divides k then a.den k else a

def coeff (axis : Nat) (a : Lin) := if axis=0 then a.j else if axis=1 then a.i else a.t

def tighten (xs : List Lin) : List Lin := xs.filter fun a =>
  !xs.any (fun b => b.t==a.t && b.i==a.i && b.j==a.j && b.d<a.d)

def elim (axis : Nat) (xs : List Lin) : List Lin :=
  let c := coeff axis
  let low := xs.filter fun a => 0 < c a
  let high := xs.filter fun a => c a < 0
  tighten (((xs.filter fun a => c a == 0) ++ low.flatMap (fun a =>
    high.map (fun b => ((a.mul (-c b)).add (b.mul (c a))).norm))).eraseDups)

def clash (xs : List Lin) := xs.any fun a =>
  a.t==0 && a.i==0 && a.j==0 && a.d<0

def ordered (x y z : Nat) (xs : List Lin) : Bool :=
  let a := elim x xs
  let b := elim y a
  clash a || clash b || clash (elim z b)

def impossible (xs : List Lin) : Bool := clash xs || ordered 0 1 2 xs

def fallback (xs : List Lin) : Bool :=
  impossible xs || ordered 1 0 2 xs || ordered 2 1 0 xs || ordered 2 0 1 xs ||
    ordered 1 2 0 xs || ordered 0 2 1 xs

inductive Formula
  | yes | no | test (a : Lin) | both (p q : Formula) | either (p q : Formula)
  deriving Inhabited

def Formula.neg : Formula → Formula
  | .yes => .no | .no => .yes | .test a => .test a.neg
  | .both p q => .either p.neg q.neg
  | .either p q => .both p.neg q.neg

def Formula.band : Formula → Formula → Formula
  | .no,_ | _,.no => .no
  | .yes,b => b | a,.yes => a
  | a,b => .both a b

def Formula.bor : Formula → Formula → Formula
  | .yes,_ | _,.yes => .yes
  | .no,b => b | a,.no => a
  | a,b => .either a b

def Formula.weight : Formula → Nat
  | .both p q | .either p q => p.weight+q.weight+1
  | _ => 1

def refute : Nat → List Lin → List Formula → Bool
  | _,cs,[] => impossible cs
  | 0,cs,_ => impossible cs
  | fuel+1,cs,p::ps =>
    match p with
    | .yes => refute fuel cs ps
    | .no => true
    | .test a => refute fuel (a::cs) ps
    | .both a b => refute fuel cs (a::b::ps)
    | .either a b => impossible cs || (refute fuel cs (a::ps) && refute fuel cs (b::ps))

def reduced (cs : List Lin) : Formula → Formula
  | .test a =>
    if cs.any (·.entails a) then .yes else if cs.any (·.entails a.neg) then .no else .test a
  | .yes => .yes | .no => .no
  | .both a b => (reduced cs a).band (reduced cs b)
  | .either a b => (reduced cs a).bor (reduced cs b)

def firstAtom : Formula → Lin
  | .test a => a | .both p _ | .either p _ => firstAtom p | _ => default

def solve : Nat → List Lin → Formula → Bool
  | 0,cs,_ => impossible cs
  | fuel+1,cs,p =>
    match reduced cs p with
    | .no => true
    | .yes => fallback cs
    | q => impossible cs || (let a := firstAtom q
        solve fuel (a::cs) q && solve fuel (a.neg::cs) q)

end GridGraphs.ResidueTwoLower.Poly
