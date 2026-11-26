import GridGraphs.ResidueTwoUpper.ExceptionalMessages

/-! An unaveraged mod-two charge on real local incidences. Depth four,
period six; one normalization bit at the southeast patch. A table entry
stores the entire set of accepted event words in a 64-bit bitmap. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.Parity
open ResidueZero Stencil Finset

def masks : Std.HashMap Nat Nat := .ofList <|
  ((include_str "Data/exceptional.parity").splitOn "\n").filterMap fun s =>
    match s.splitOn " " with
    | [a,b] => do return (←a.toNat?,←b.toNat?)
    | _ => none
def ax (s i : Int) := if i<4 then i else if s-4 ≤ i then 14+i-s else 4+(i-4)%6
def bucket (s : Int) (p : Pos) := (ax s p.1).toNat*32+(ax s p.2).toNat
def price (kind pos q ev : Nat) : Int := ((masks.getD (kind*10000+pos*9+q) 0).testBit ev).toNat

def bond (kind : Nat) (s : Int) (p : Pos) (d ev : Nat) : Int :=
  let v := shift p d
  if inside s v then
    if d<2 then price kind (bucket s p) d ev else -price kind (bucket s v) (d-2) ev
  else 0
def port (s : Int) (p : Pos) (f nb o d : Nat) :=
  bond 2 s p d (edgeEvent f (bit nb d) o d)
def strip (s : Int) (p : Pos) (m d : Nat) := bond 3 s p d (overlapBits m d)
def cover (n : Int) (p : Pos) (f nb q : Nat) :=
  let a := p-offset q
  if inside (n-2) a then price 4 (bucket (n-2) a) q (localEvent q f nb) else 0
def slot (n : Int) (a : Pos) (m q : Nat) :=
  price 4 (bucket (n-2) a) q (localEvent q (bit m q) (patchNbr m q))
def special (s : Int) (p : Pos) : Int := if bucket s p=429 then 1 else 0
def starBill (n : Int) (p : Pos) (f nb o : Nat) :=
  (∑ d : Fin 4, port n p f nb o d) + ∑ q : Fin 9, cover n p f nb q
def patchBill (n : Int) (a : Pos) (m : Nat) :=
  special (n-2) a + (∑ d : Fin 4, strip (n-2) a m d) - ∑ q : Fin 9, slot n a m q

def rootOK (n : Int) (p : Pos) (o : Nat) :=
  if p=(0,0) then o==4
  else if (p.1=0 ∨ p.1=n-1) ∧ (p.2=0 ∨ p.2=n-1) then o != 4 else true

def starCheck : Bool := decide (∀ i j : Fin 35, ∀ f : Fin 2, ∀ nb : Fin 16, ∀ o : Fin 5,
  let p : Pos := (i.val,j.val)
  starOK 35 p f nb o → rootOK 35 p o →
    let w := twoOrbitStar 35 p f nb o
    w=0 ∨ w=half → starBill 35 p f nb o % 2=0)
def patchCheck : Bool := decide (∀ i j : Fin 33, ∀ m : Fin 512,
  let a : Pos := (i.val,j.val)
  maskOK m → let w := twoOrbitPatch 35 a m
  w=0 ∨ w=half → patchBill 35 a m % 2=0)

end GridGraphs.ResidueTwoUpper.Exceptional.Parity
