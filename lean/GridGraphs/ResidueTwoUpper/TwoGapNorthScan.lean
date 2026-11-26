import GridGraphs.ResidueTwoUpper.TwoGapNorthPhase

/-! A single side-35 strip with a three-column insertion loop.
Search only for a counterexample to alignment: the distinguished
exit, if visible, must be at the wrong phase. All costs are the
physical integer stencil costs, computed here from the price tables. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
open ResidueZero Stencil
def preset (j r : Nat) : Option Nat :=
  if r=0 then some (if j=1 ∨ j=2 then 0 else 1)
  else if j=0 then some 1
  else if j=34 then some (if r=1 ∨ r=2 then 0 else 1)
  else if r=1 ∨ j=1 ∨ j=33 then some 0 else none
def column (j m : Nat) := (List.range 6).all fun r =>
  (preset j r).all fun f => bit m r==f
def opts := Array.ofFn fun j : Fin 35 => (List.range 64).filter (column j)
def pack3 (m r : Nat) := bit m r+8*bit m (r+1)+64*bit m (r+2)
def window (a b c r : Nat) := pack3 a r+2*pack3 b r+4*pack3 c r
def patch (j r m : Nat) := maskOK m && twoOrbitPatch 35 (r,j) m==0
def pt := Array.ofFn fun j : Fin 33 => Array.ofFn fun r : Fin 4 =>
  Array.ofFn fun m : Fin 512 => patch j r m
def patchPass (j a b c : Nat) := j==0 || j==34 || (List.range 4).all fun r =>
  (((pt[j-1]!)[r]!)[window a b c r]!)
def cornerStar (j r f nb o : Nat) :=
  let root := j=0 ∧ r=0
  let w := twoOrbitStar 35 (r,j) f nb o
  starOK 35 (r,j) f nb o && (if root then o==4 else o != 4 || (f==0 && nb==0)) &&
    (w==0 || (w==full && r==0 && o==1 && j≥3 && j<34 && j != 32 && j%3 != 2))
def st := Array.ofFn fun j : Fin 35 => Array.ofFn fun r : Fin 5 =>
  Array.ofFn fun f : Fin 2 => Array.ofFn fun nb : Fin 16 =>
    (List.range 5).filter (cornerStar j r f nb)
def nbAt (a b c r : Nat) := bit c r+2*bit b (r+1)+4*bit a r+
  (if r=0 then 0 else 8*bit b (r-1))
def dirs (j r a b c : Nat) := if r=5 then [0,1,2,3,4] else
  (((st[j]!)[r]!)[bit b r]!)[nbAt a b c r]!
def beltFull (t a b c : Nat) :=
  let endOK (m : Nat) := ((m ||| (m>>>1)) &&& 15)==15
  let horiz (x y : Nat) := ((x ||| y) &&& 17)==17
  endOK t && endOK c && horiz t a && horiz a b && horiz b c

-- Enumerate edge owners row by row. State: whether the preceding row
-- points down, and the next column's already-owned westward arrows.
def rowStep (j a b c west r : Nat) (s : Bool × Nat) : List (Bool × Nat) :=
  (dirs j r a b c).filterMap fun d => Id.run do
    if (d==2)  !=  (bit west r==1) then return none
    let up := d==3
    let vertical := r != 0 && (bit b r+bit b (r-1)>0)
    if s.1.toNat+up.toNat != vertical.toNat then return none
    let horizontal := j != 34 && (bit b r+bit c r>0)
    if d==0 && !horizontal then return none
    return some (d==1,s.2+(if horizontal && d != 0 then 2^r else 0))
def owners (j a b c west : Nat) := ((List.range 6).foldl
  (fun states r => states.flatMap (rowStep j a b c west r)) [(false,0)]).map Prod.snd

abbrev State := Nat × Nat × Nat × Nat
def next (j : Nat) (s : State) : List State :=
  let (t,a,b,west) := s
  (if j==34 then [0] else opts[j+1]!).flatMap fun c =>
    if !patchPass j a b c || (j != 34 && beltFull t a b c) then [] else
    (owners j a b c west).map fun w => (a,b,c,w)
def reach : Nat → List State
  | 0 => opts[0]!.map fun b => (0,0,b,0)
  | j+1 => ((reach j).flatMap (next j)).eraseDups
def middle := (reach 26).all (reach 23).contains
def empty := (reach 35).isEmpty

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
