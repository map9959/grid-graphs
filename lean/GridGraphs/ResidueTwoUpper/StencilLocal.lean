import GridGraphs.ResidueTwoUpper.StencilPrices
import GridGraphs.ResidueZero.LocationTransport

namespace GridGraphs.ResidueTwoUpper.Stencil
open GridGraphs.ResidueZero hiding scale starNormPrices patchNormPrices edgePrices incidencePrices overlapPrices cornerPrices

def twoPort (l : StarLocation) (f nb o d : Nat) : Int :=
  match l.neighbour d with
  | none => 0
  | some u =>
    let e := edgeEvent f (bit nb d) o d
    if d<2 then edgePrices.getD (key l.t u d e) 0
    else -(edgePrices.getD (key u l.t (d-2) e) 0)

def twoCoverTerm (l : StarLocation) (f nb q : Nat) : Int :=
  match l.cover q with
  | none => 0
  | some a => incidencePrices.getD (key a l.t q (localEvent q f nb)) 0

def twoStarBill (l : StarLocation) (f nb o : Nat) : Int :=
  (starNormPrices.getD l.ft 0-scale*(f:Int) + (if o=4 then 4*cornerPrices.getD l.ft 0 else 0)) +
  (∑ d ∈ Finset.range 4, twoPort l f nb o d) + ∑ q ∈ Finset.range 9, twoCoverTerm l f nb q

def twoSlotTerm (l : PatchLocation) (m q : Nat) : Int :=
  incidencePrices.getD (key l.t (l.site q) q (localEvent q (bit m q) (patchNbr m q))) 0

def twoStripTerm (l : PatchLocation) (m d : Nat) : Int :=
  match l.neighbour d with
  | none => 0
  | some u =>
    let e := overlapBits m d
    if d<2 then overlapPrices.getD (key l.t u d e) 0
    else -(overlapPrices.getD (key u l.t (d-2) e) 0)

def twoPatchBill (l : PatchLocation) (m : Nat) : Int :=
  patchNormPrices.getD l.ft 0 - (∑ q ∈ Finset.range 9, twoSlotTerm l m q) +
    ∑ d ∈ Finset.range 4, twoStripTerm l m d

def twoOrbitStar (n : Int) (p : Pos) (f nb o : Nat) :=
  ((List.range 8).map fun g => twoStarBill (starLocation n (image n g p)) f (rotBits g nb)
    (if o==4 then 4 else turn g o)).sum

def twoOrbitPatch (n : Int) (p : Pos) (m : Nat) :=
  ((List.range 8).map fun g => twoPatchBill (patchLocation (n-2) (image (n-2) g p)) (rotMask g m)).sum

def twoStarCheck (n : Nat) := (List.range n).all fun r => (List.range n).all fun c =>
  let p : Pos := (r,c)
  (List.range 2).all fun f => (List.range 16).all fun nb => (List.range 5).all fun o =>
    !starOK n p f nb o || 0 ≤ twoOrbitStar n p f nb o

def twoPatchCheck (n : Nat) := (List.range (n-2)).all fun r => (List.range (n-2)).all fun c =>
  let p : Pos := (r,c)
  (List.range 512).all fun m => !maskOK m || 0 ≤ twoOrbitPatch n p m

end GridGraphs.ResidueTwoUpper.Stencil
