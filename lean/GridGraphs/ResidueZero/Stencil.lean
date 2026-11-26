import GridGraphs.ResidueZero.Prices
import GridGraphs.ResidueZero.Transport

/-! Unpooled signed charges. Directions are east, south, west, north.
The signed terms are endpoint contributions of edge, star/patch and
patch/patch equalities; no optimization or fitted slacks are used. -/
namespace GridGraphs.ResidueZero

abbrev Pos := Int × Int

def atPos (n d : Int) (p : Pos) : Nat :=
  (axis n d p.1).toNat*16+(axis n d p.2).toNat

def inside (n : Int) (p : Pos) : Bool :=
  0 ≤ p.1 && p.1 < n && 0 ≤ p.2 && p.2 < n

def shift (p : Pos) (d : Nat) : Pos :=
  match d with
  | 0 => (p.1,p.2+1)
  | 1 => (p.1+1,p.2)
  | 2 => (p.1,p.2-1)
  | _ => (p.1-1,p.2)

def offset (q : Nat) : Pos := (q/3,q%3)
def posIdx (p : Pos) := p.1.toNat*3+p.2.toNat
def bit (m i : Nat) := (m >>> i) % 2
def key (p t idx event : Nat) := ((p*256+t)*9+idx)*64+event

/-- First event bit is the centre, followed by the neighbours inside
the window in compass order. -/
def localEvent (q f nb : Nat) : Nat := Id.run do
  let mut v := f
  let mut w := 2
  for d in [:4] do
    if inside 3 (shift (offset q) d) then
      v := v+w*bit nb d
      w := w*2
  return v

@[ext] structure StarLocation where
  t : Nat
  ft : Nat
  neighbour : Nat → Option Nat
  cover : Nat → Option Nat

def located (s : Int) (a : Pos) : Option Nat :=
  if inside s a then some (atPos s 2 a) else none

def starLocation (n : Int) (p : Pos) : StarLocation :=
  ⟨atPos n 2 p, atPos n 6 p, fun d => located n (shift p d),
    fun q => if q<9 then located (n-2) (p-offset q) else none⟩

def edgeEvent (f b o d : Nat) :=
  let forward := d<2
  let arrow := if f+b==0 then 1 else if (o==d)==forward then 2 else 0
  3*(if forward then 2*f+b else 2*b+f)+arrow

def port (l : StarLocation) (f nb o d : Nat) : Int :=
  match l.neighbour d with
  | none => 0
  | some u =>
    let e := edgeEvent f (bit nb d) o d
    if d<2 then edgePrices.getD (key l.t u d e) 0
    else -(edgePrices.getD (key u l.t (d-2) e) 0)

def coverTerm (l : StarLocation) (f nb q : Nat) : Int :=
  match l.cover q with
  | none => 0
  | some a => incidencePrices.getD (key a l.t q (localEvent q f nb)) 0

def starBill (l : StarLocation) (f nb o : Nat) : Int :=
  (starNormPrices.getD l.ft 0-scale*(f:Int) + (if o=4 then 4*cornerPrices.getD l.ft 0 else 0)) +
  (∑ d ∈ Finset.range 4, port l f nb o d) + ∑ q ∈ Finset.range 9, coverTerm l f nb q

@[ext] structure PatchLocation where
  t : Nat
  ft : Nat
  site : Nat → Nat
  neighbour : Nat → Option Nat

def patchLocation (s : Int) (p : Pos) : PatchLocation :=
  ⟨atPos s 2 p, atPos s 5 p, fun q => if q<9 then atPos (s+2) 2 (p+offset q) else 0,
    fun d => located s (shift p d)⟩

def patchNbr (m q : Nat) : Nat := Id.run do
  let mut nb := 0
  for d in [:4] do
    let u := shift (offset q) d
    if inside 3 u then nb := nb+(bit m (posIdx u) <<< d)
  return nb

def overlapBits (m d : Nat) : Nat := Id.run do
  let mut w := 1
  let mut e := 0
  for q in [:9] do
    if inside 3 (shift (offset q) ((d+2)%4)) then
      e := e+w*bit m q
      w := w*2
  return e

def slotTerm (l : PatchLocation) (m q : Nat) : Int :=
  incidencePrices.getD (key l.t (l.site q) q (localEvent q (bit m q) (patchNbr m q))) 0

def stripTerm (l : PatchLocation) (m d : Nat) : Int :=
  match l.neighbour d with
  | none => 0
  | some u =>
    let e := overlapBits m d
    if d<2 then overlapPrices.getD (key l.t u d e) 0
    else -(overlapPrices.getD (key u l.t (d-2) e) 0)

def patchBill (l : PatchLocation) (m : Nat) : Int :=
  patchNormPrices.getD l.ft 0 - (∑ q ∈ Finset.range 9, slotTerm l m q) +
    ∑ d ∈ Finset.range 4, stripTerm l m d

def turn (g d : Nat) := ((if g≥4 then 6-d else d)+g%4)%4
def image (s : Int) (g : Nat) (p : Pos) : Pos :=
  let r := p.1
  let c := if g≥4 then s-1-p.2 else p.2
  match g%4 with
  | 0 => (r,c)
  | 1 => (c,s-1-r)
  | 2 => (s-1-r,s-1-c)
  | _ => (s-1-c,r)

def rotBits (g nb : Nat) :=
  ((List.range 4).map fun d => (bit nb d <<< turn g d)).sum
def rotMask (g m : Nat) :=
  ((List.range 9).map fun q => bit m q <<< posIdx (image 3 g (offset q))).sum

def starOK (n : Int) (p : Pos) (f nb o : Nat) : Bool :=
  ((List.range 4).all fun d => bit nb d == 0 ||
    (inside n (shift p d) && bit nb ((d+1)%4) == 0)) &&
    (o == 4 || (inside n (shift p o) && 0 < f+bit nb o))

/-- Minimal vertex covers forcing a cycle in the 3×3 grid. -/
def maskOK (m : Nat) : Bool :=
  [10,17,20,34,45,80,136,160,195,272,325,360,390].all fun c => (m &&& c) != c

def orbitStar (n : Int) (p : Pos) (f nb o : Nat) :=
  ((List.range 8).map fun g => starBill (starLocation n (image n g p)) f (rotBits g nb)
    (if o==4 then 4 else turn g o)).sum

def orbitPatch (n : Int) (p : Pos) (m : Nat) :=
  ((List.range 8).map fun g => patchBill (patchLocation (n-2) (image (n-2) g p)) (rotMask g m)).sum

def starCheck (n : Nat) := (List.range n).all fun r => (List.range n).all fun c =>
  let p : Pos := (r,c)
  (List.range 2).all fun f => (List.range 16).all fun nb => (List.range 5).all fun o =>
    !starOK n p f nb o || 0 ≤ orbitStar n p f nb o

def patchCheck (n : Nat) := (List.range (n-2)).all fun r => (List.range (n-2)).all fun c =>
  let p : Pos := (r,c)
  (List.range 512).all fun m => !maskOK m || 0 ≤ orbitPatch n p m

end GridGraphs.ResidueZero
