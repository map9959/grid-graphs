import GridGraphs.Results.SmallDiagonalExact.Eleven.Prices
import GridGraphs.ResidueZero.LocationTransport

namespace GridGraphs.Eleven
open GridGraphs.ResidueZero hiding scale starNormPrices patchNormPrices edgePrices incidencePrices overlapPrices cornerPrices

/-! Physical marginal keys use actual row and column, since the finite
certificate has no periodic identifications. The normalization keys retain
`atPos` to reuse the grid normalization sum. -/
def raw (p : Pos) : Nat := p.1.toNat*16+p.2.toNat
def here (s : Int) (p : Pos) : Option Nat := if inside s p then some (raw p) else none
def starLoc (n : Int) (p : Pos) : StarLocation :=
  ⟨raw p, atPos n 6 p, fun d => here n (shift p d),
    fun q => if q<9 then here (n-2) (p-offset q) else none⟩
def patchLoc (s : Int) (p : Pos) : PatchLocation :=
  ⟨raw p, atPos s 5 p, fun q => if q<9 then raw (p+offset q) else 0,
    fun d => here s (shift p d)⟩

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
  ((List.range 8).map fun g => twoStarBill (starLoc n (image n g p)) f (rotBits g nb)
    (if o==4 then 4 else turn g o)).sum

def twoOrbitPatch (n : Int) (p : Pos) (m : Nat) :=
  ((List.range 8).map fun g => twoPatchBill (patchLoc (n-2) (image (n-2) g p)) (rotMask g m)).sum

def twoStarCheck (n : Nat) := (List.range n).all fun r => (List.range n).all fun c =>
  let p : Pos := (r,c)
  (List.range 2).all fun f => (List.range 16).all fun nb => (List.range 5).all fun o =>
    !starOK n p f nb o || 0 ≤ twoOrbitStar n p f nb o

def twoPatchCheck (n : Nat) := (List.range (n-2)).all fun r => (List.range (n-2)).all fun c =>
  let p : Pos := (r,c)
  (List.range 512).all fun m => !maskOK m || 0 ≤ twoOrbitPatch n p m

theorem fromStar {n : Nat} (checked : twoStarCheck n) {p : Pos} (hp : inside n p)
    {f nb o : Nat} (hf : f<2) (hn : nb<16) (ho : o<5) (ok : starOK n p f nb o) :
    0 ≤ twoOrbitStar n p f nb o := by
  simp [twoStarCheck,List.all_eq_true] at checked
  simp [inside] at hp
  have H := checked p.1.toNat (by omega) p.2.toNat (by omega) f (by omega) nb (by omega) o (by omega)
  simpa [Int.toNat_of_nonneg (by omega : 0≤p.1),Int.toNat_of_nonneg (by omega : 0≤p.2),ok] using H

theorem fromPatch {n : Nat} (checked : twoPatchCheck n) {p : Pos} (hp : inside (n-2:Nat) p)
    {m : Nat} (hm : m<512) (ok : maskOK m) : 0 ≤ twoOrbitPatch n p m := by
  simp [twoPatchCheck,List.all_eq_true] at checked
  simp [inside] at hp
  have H := checked p.1.toNat (by omega) p.2.toNat (by omega) m hm
  simpa [Int.toNat_of_nonneg (by omega : 0≤p.1),Int.toNat_of_nonneg (by omega : 0≤p.2),ok] using H

end GridGraphs.Eleven
