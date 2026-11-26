import GridGraphs.ResidueZero.PhysicalSum
import GridGraphs.ResidueZero.Normalization
import GridGraphs.Results.CombLower

namespace GridGraphs.FiniteOne
open ResidueZero Finset

/-- A price vector is indexed by a physical incidence and its shared word.
No assumption on how it was obtained (or how accurately it was rounded). -/
structure Prices where
  unit : Nat
  dict : Array (Array Int)
  ids : Array Nat
  deriving Inhabited
def Prices.get (T : Prices) (i w : Nat) := ((T.dict[T.ids[i]?.getD 0]?).getD #[])[w]?.getD 0
def idx (s : Nat) (p : Pos) := p.1.toNat*s+p.2.toNat
def bond (T : Prices) (base s : Nat) (p : Pos) (d w : Nat) : Int :=
  let q := shift p d
  if inside s q then
    if d<2 then T.get (base+2*idx s p+d) w else -T.get (base+2*idx s q+(d-2)) w
  else 0
def slot (T : Prices) (n : Nat) (a : Pos) (q w : Nat) :=
  T.get (2*n*n+2*(n-2)*(n-2)+9*idx (n-2) a+q) w
def cover (T : Prices) (n : Nat) (p : Pos) (q w : Nat) :=
  if inside (n-2:Nat) (p-offset q) then slot T n (p-offset q) q w else 0
def portAt (T : Prices) (n : Nat) (p : Pos) (f nb o d : Nat) :=
  bond T 0 n p d (edgeEvent f (bit nb d) o d)
def stripAt (T : Prices) (n : Nat) (p : Pos) (m d : Nat) :=
  bond T (2*n*n) (n-2) p d (overlapBits m d)
def coverAt (T : Prices) (n : Nat) (p : Pos) (f nb q : Nat) :=
  cover T n p q (localEvent q f nb)
def slotAt (T : Prices) (n : Nat) (p : Pos) (m q : Nat) :=
  slot T n p q (localEvent q (bit m q) (patchNbr m q))
def starCost (T : Prices) (n : Nat) (p : Pos) (f nb o : Nat) :=
  (T.unit:Int)*f - (∑ d ∈ range 4, portAt T n p f nb o d) - ∑ q : Fin 9, coverAt T n p f nb q
def patchCost (T : Prices) (n : Nat) (p : Pos) (m : Nat) :=
  (∑ q : Fin 9, slotAt T n p m q) - ∑ d ∈ range 4, stripAt T n p m d

abbrev Atom := Fin 2 × Fin 16 × Fin 5
def allowed (n : Nat) (p : Pos) (a : Atom) :=
  starOK n p a.1 a.2.1 a.2.2 && (p != (0,0) || a.2.2.val==4)
def bottom : Int := -1000000000000000
def starMax (T : Prices) (n : Nat) (p : Pos) :=
  (univ : Finset Atom).sup' univ_nonempty fun a =>
    if allowed n p a then starCost T n p a.1 a.2.1 a.2.2 else bottom
def masks := (univ : Finset (Fin 512)).filter fun (m : Fin 512) => maskOK m.val
def patchMax (T : Prices) (n : Nat) (p : Pos) :=
  masks.sup' (by exact ⟨0,mem_filter.mpr ⟨mem_univ _,by decide⟩⟩) fun m => patchCost T n p m
def budget (T : Prices) (n : Nat) := (∑ p : GridVertex n n, starMax T n (coord p))+
  ∑ p : origins n, patchMax T n (coord p)

private abbrev Parser := StateT Nat Option
private def readN (b : ByteArray) : Nat → Parser Nat
  | 0 => failure
  | t+1 => do
    let i ← get; let v ← b[i]?.map UInt8.toNat; set (i+1)
    guard (48≤v && v<112)
    if v<80 then return v-48 else return v-80+32*(←readN b t)
def decode (n : Nat) (s : String) : Prices := Id.run do
  let b := s.toUTF8
  let parse : Parser Prices := do
    let u := readN b 20
    let unit ← u; let count ← u
    let mut dict := #[#[]]
    for _ in [:count] do
      let len ← u
      let mut row : Array Int := Array.replicate 64 0
      for _ in [:len] do
        let w ← u; let z ← u
        row := row.setIfInBounds w (if z%2=0 then (z/2:Nat) else -((z/2:Nat):Int)-1)
      dict := dict.push row
    let mut ids := #[]
    for _ in [:2*n*n+11*(n-2)*(n-2)] do ids := ids.push (←u)
    return ⟨unit,dict,ids⟩
  return (parse.run' 0).getD default
end GridGraphs.FiniteOne
