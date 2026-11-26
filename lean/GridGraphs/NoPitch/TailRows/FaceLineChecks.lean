import GridGraphs.NoPitch.TailRows.OverlapCensus
import GridGraphs.NoPitch.FaceLineIncidence
import GridGraphs.NoPitch.TailRows.IncidenceViews

namespace GridGraphs.NoPitch.TailRows.FaceLine
open PitchCut Keys FaceRows Wired Budget LocalBoard19 GridGraphs.NoPitch.Dual

structure Book where
  start : Nat
  tags : Array Nat

def oddBook : Book := ⟨3541,#[23,24,27,30,3,6,7,11,15,112,114,115,116,118,119,122,124,126,127,
  97,101,105,109,208,210,211,213,220,222,223,694,695,697,698,699,703,675,678,686,687,786,787,791,
  792,796,799,771,774,780,782,783,880,882,883,885,889,892,893,1347,1350,1351,1353,1354,1355,
  1440,1462,1463,1465,1466,1467,1470,1471,1442,1444,1446,1447,1454,1554,1558,1562,1566,1545,1548,1549]⟩
def evenBook : Book := ⟨3483,#[18,19,20,22,26,30,31,115,118,119,123,124,126,127,97,99,101,102,105,
  106,110,198,672,688,692,694,695,696,700,702,673,676,678,679,682,683,687,785,788,791,774,780,782,
  783,880,882,883,884,885,886,887,893,1344,1346,1347,1351,1355,1356,1357,1358,1359,1458,1462,
  1466,1470,1446,1449,1453,1545]⟩
def Book.sel (B : Book) (i : Nat) := B.start ≤ i && i < B.start+B.tags.size
def Book.table (B : Book) : Array Terms := Id.run do
  let mut t := Array.replicate 1568 []
  for h : i in [:B.tags.size] do
    t := t.setIfInBounds B.tags[i] [(B.start+i,1)]
  return t

def axisLabel (k x : Nat) := if x=0 then 0 else if x+1=k then 6 else 3
def stamp (T : Array Terms) (k r c a w : Nat) :=
  T[(((axisLabel k r*7+axisLabel k c)*2+a)*16+w)]?.getD []
def tile {k} [NeZero k] (T : Array Terms) (p : FacePos k) (m : Mask) :=
  (List.finRange 8).flatMap fun g => (List.finRange 2).flatMap fun (a : Fin 2) =>
    let q := small k g p
    stamp T k q.1 q.2 a (FaceLines.rotWord g m a)
def arc (T : Array Terms) (k r j : Nat) (s t : State) :=
  if j=0 then [] else
  (if r<k then stamp T k r (j-1) 0 (FaceLines.stepWord s t) else []) ++
  (if r=0 then [] else stamp T k (r-1) (j-1) 1 (FaceLines.stepWord s t))

def srcOK (D : Chart) (B : Book) :=
  let masks := supportMasks D
  decide (∀ i : Fin D.rows.size, masks[i]! = 12 ↔ B.sel i) &&
  D.cols.all (fun c => c.key%8==2 || c.key%8==3 || c.terms.all fun t => !B.sel t.1)

@[noinline] def arcOK (b : Nat) (w : Nat → Terms) (T : Array Terms) :=
  decide (∀ r j : J b, ∀ s∈layers (min j.val 4), ∀ a : Letter, permit b j s a →
    balanced (w (arcKey (band b r) (prior b j) (band b j) s (advance s a)) ++ arc T b r j s (advance s a)))

/-- A face origin has only three axis labels (low, interior, high).
Thus nine position representatives suffice, including all eight views. -/
def pos (j : Fin 9) : FacePos 3 := (Fin.ofNat 3 (j.val/3),Fin.ofNat 3 j.val)
@[noinline] def positions (w : Nat → Terms) (cost : Vector Terms 9) (vs : Vector Nat 8) :=
  decide (∀ j : Fin 9, balanced (w (keyAt (pos j) vs) ++ cost[j]))
@[noinline] def parts (w : Nat → Terms) (cost : Vector Terms 9) (m : Mask) :=
  (catalog m).all fun z => positions w cost (faceViews m (partOf z))
@[noinline] def tilesOK (w : Nat → Terms) (T : Array Terms) :=
  decide (∀ i : Fin 65536, let m := maskOf i
    fresh initial (rawEdges m) →
    parts w (Vector.ofFn fun j => negTerms (tile T (pos j) m)) m)

def cert (D : Chart) (B : Book) (b : Nat) :=
  let w := contribution D (index D) (prices D B.sel)
  srcOK D B && arcOK b w B.table && tilesOK w B.table
end GridGraphs.NoPitch.TailRows.FaceLine
