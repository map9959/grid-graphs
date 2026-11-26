import GridGraphs.NoPitch.PhysicalKeys
import GridGraphs.NoPitch.ColumnProjection

namespace GridGraphs.NoPitch.Wired
open PitchCut Keys

abbrev V := Fin 16
abbrev E := V × V
def cell (x : V) : Fin 4 × Fin 4 := (Fin.ofNat 4 (x.val/4),Fin.ofNat 4 x.val)
def vid (r c : Fin 4) : V := ⟨4*r.val+c.val,by have := r.isLt; have := c.isLt; omega⟩
def es : List E := (List.finRange 16).flatMap fun x =>
  (if x.val%4<3 then [(x,Fin.ofNat 16 (x.val+1))] else []) ++
  (if x.val<12 then [(x,Fin.ofNat 16 (x.val+4))] else [])
def rim (x : V) := x.val/4==0 || x.val/4==3 || x.val%4==0 || x.val%4==3
def marked (m : Mask) (x : V) := m (cell x).1 (cell x).2
def old (m : Mask) (e : E) := (marked m e.1 && rim e.1) || (marked m e.2 && rim e.2)
def extra (m : Mask) (e : E) := (marked m e.1 || marked m e.2) && !old m e
def baseEdges (m : Mask) := es.filter (old m)
def newEdges (m : Mask) := es.filter (extra m)

abbrev Labels := Vector V 16
def initial : Labels := Vector.ofFn id
def merge (s : Labels) (e : E) : Labels := s.map fun v => if v=s[e.2] then s[e.1] else v
def base (m : Mask) := (baseEdges m).foldl merge initial

def corners := (List.finRange 2).flatMap fun i => (List.finRange 2).map (i,·)
def cpairs := corners.flatMap fun c => corners.map (c,·)
def cv (c : Corner) := vid (cornerOffset c.1) (cornerOffset c.2)
def wires (q : PartitionBits) := (cpairs.filter fun (c,d) => q c d).map (fun (c,d) => (cv c,cv d))
def consistent (s : Labels) (q : PartitionBits) := cpairs.all fun (c,d) =>
  s[cv c]!=s[cv d] || q c d

def fresh (s : Labels) : List E → Bool
  | [] => true
  | e::rest => s[e.1]!=s[e.2] && fresh (merge s e) rest

/-- Build the perimeter skeleton, then identify corners already joined
outside, then insert only edges newly forced by this face. -/
def compatible (m : Mask) (q : PartitionBits) :=
  fresh initial (baseEdges m) && consistent (base m) q &&
    fresh ((wires q).foldl merge (base m)) (newEdges m)

def maskOf (m : Nat) : Mask := fun r c => m.testBit (4*r.val+c.val)
def partOf (z : Nat) : PartitionBits :=
  let color (c : Corner) := (z/4^(2*c.1.val+c.2.val))%4
  fun c d => color c==color d

/-- Enumerate one base-four code per equivalence relation (labels are
the least index in each class, rather than compressed run numbers). -/
def colorCode (q : PartitionBits) :=
  ((List.range 4).map fun i =>
    let c (j : Nat) : Corner := (Fin.ofNat 2 (j/2),Fin.ofNat 2 j)
    (((List.range 4).find? fun j => q (c i) (c j)).getD i)*4^i).sum
def partitions := (List.range 256).filter fun z => colorCode (partOf z)==z

def catalog (m : Mask) := partitions.filter fun z => compatible m (partOf z)

def rawEdges (m : Mask) := es.filter (fun e => marked m e.1 || marked m e.2)
def lookupAll (D : Dual.Chart) (k : Nat) :=
  let idx := Dual.index D
  decide (∀ i : Fin 65536, let m := maskOf i
    fresh initial (rawEdges m) → ∀ z∈catalog m, let v := faceViews m (partOf z)
      ∀ p : FacePos k, (Dual.locate D idx (keyAt p v)).isSome=true)

end GridGraphs.NoPitch.Wired
