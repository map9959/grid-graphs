import GridGraphs.NoPitch.FaceRows
import GridGraphs.NoPitch.LineKeys19

namespace GridGraphs.NoPitch.FaceLines
open GridGraphs.NoPitch.Dual PitchCut Keys Wired FaceRows Finset

abbrev Pos := FacePos 6
abbrev Slot := Fin 7 × Fin 7
def kept (i : Nat) := 2790 ≤ i && i ≤ 2870
def entries (c : Col) : Terms :=
  (c.terms.filter fun t => kept t.1).map fun t => (t.1,t.2*c.units)
def charges (D : Chart) := contribution D (index D) (D.cols.map entries)

/-- Suggested boundary labels, in retained-row order. The checks below
compare their expansions with the actual matrix coefficients. -/
def tokens : Array Nat := #[18,20,22,23,24,27,121,97,101,102,103,108,110,111,209,210,211,213,221,222,
  223,688,690,691,694,695,700,702,703,674,675,676,678,679,681,683,686,687,792,794,795,776,778,
  779,881,889,893,866,867,869,870,871,873,874,875,877,1344,1372,1373,1374,1375,1348,1354,
  1356,1358,1359,1457,1458,1459,1461,1462,1463,1468,1470,1471,1561,1562,1563,1538,1539,1541]
def marks : Array Terms := Id.run do
  let mut a := Array.replicate 1568 []
  for h : i in [:tokens.size] do
    a := a.setIfInBounds tokens[i] [(2790+i,1)]
  return a

def stamp (p : Pos) (a : Fin 2) (word : Nat) : Terms :=
  marks[(((axis 16 2 (3*p.1.val)*7+axis 16 2 (3*p.2.val))*2+a.val)*16+word)]?.getD []

def rotPos (g : Fin 8) (p : Pos) : Pos := small 6 g p
def rotWord (g : Fin 8) (m : Mask) (a : Fin 2) :=
  (List.range 4).foldl (fun n b =>
    let q := small 4 (invers g) (cornerOffset a,Fin.ofNat 4 b)
    n+(m q.1 q.2).toNat*2^b) 0
def rotStamps (m : Mask) (p : Pos) : Terms :=
  (List.finRange 8).flatMap fun g => (List.finRange 2).flatMap fun a =>
    stamp (rotPos g p) a (rotWord g m a)

def neg (ts : Terms) := ts.map fun t => (t.1,-t.2)
def tileCheck (D : Chart) :=
  let ch := charges D
  decide (∀ i : Fin 65536, let m := maskOf i
    fresh initial (rawEdges m) →
    let stamps := Vector.ofFn (n:=36) fun j =>
      neg (rotStamps m (Fin.ofNat 6 (j.val/6),Fin.ofNat 6 j.val))
    ∀ z∈catalog m, let vs := faceViews m (partOf z)
      ∀ p : Pos, balanced (ch (keyAt p vs) ++ stamps[(6*p.1.val+p.2.val)%36]))

def pointSlot (p : Pos) (a : Fin 2) : Slot :=
  (⟨p.1.val+a.val,by have := p.1.isLt; have := a.isLt; omega⟩,
   ⟨p.2.val+1,by have := p.2.isLt; omega⟩)

/-- A transition is charged once for each incident face. At the exterior
there is only one face, and the initial transition has no side at all. -/
def around (z : Slot) : List (Pos × Fin 2) :=
  if z.2.val=0 then [] else
    (if h : z.1.val<6 then [((⟨z.1.val,h⟩,Fin.ofNat 6 (z.2.val-1)),0)] else []) ++
    (if z.1.val=0 then [] else [((Fin.ofNat 6 (z.1.val-1),Fin.ofNat 6 (z.2.val-1)),1)])

def stepWord (s t : State) :=
  let a := s.prev.getD default
  let b := t.prev.getD default
  a.z.toNat+2*a.r.toNat+4*b.l.toNat+8*b.z.toNat
def lineStamps (z : Slot) (s t : State) : Terms :=
  (around z).flatMap fun (p,a) => stamp p a (stepWord s t)

def stepCheck (D : Chart) :=
  let ch := charges D
  decide (∀ (r j : Fin 7), ∀ s∈LineKeys.states j.val, ∀ a : Letter, LineKeys.allowedStep j.val s a →
    let t := advance s a
    balanced (ch (LineKeys.key r j.val s t) ++ lineStamps (r,j) s t))

def otherCheck (D : Chart) := D.cols.all fun c =>
  c.key%8==2 || c.key%8==3 || (entries c).isEmpty
def metaCheck (D : Chart) := decide (∀ i : Fin D.rows.size,
  (kept i ↔ (6064≤D.rows[i].source ∧ D.rows[i].source≤6351)) ∧
    (kept i → D.rows[i].sense=0 ∧ D.rows[i].rhs=⟨0,0,0⟩))

end GridGraphs.NoPitch.FaceLines
