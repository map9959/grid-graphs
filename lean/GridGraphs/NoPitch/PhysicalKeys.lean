import GridGraphs.Geometry.PhysicalFaceLine

namespace GridGraphs.NoPitch.Keys
open PitchCut

def pack (xs : List Nat) := xs.foldl (fun a d => 32*a+d) 0
def axis (n h z : Nat) :=
  if z<h then z else if n-h≤z then 2*h+3+z-n else h+(z-h)%3
def clip (z : Int) := ((max (-9) (min 9 z))+9).toNat
def fine (n h i j : Nat) := [axis n h i,axis n h j,clip ((i:Int)-j),clip ((i:Int)+j+1-n)]

/-- The same mirror-then-rotate convention as the certificate. -/
def transform (g : Fin 8) (n i j : Nat) : Nat × Nat :=
  let j := if g.val≥4 then n-1-j else j
  match g.val%4 with
  | 0 => (i,j)
  | 1 => (j,n-1-i)
  | 2 => (n-1-i,n-1-j)
  | _ => (n-1-j,i)

def invers (g : Fin 8) : Fin 8 :=
  ⟨if g.val≥4 then g.val else (4-g.val)%4,by split <;> omega⟩
def direction (g : Fin 8) (d : Nat) :=
  ((if g.val≥4 then 6-d else d)+g.val)%4
def minimum (f : Fin 8 → Nat) := (List.ofFn f).foldl min (f 0)

variable {k : Nat}
def probe (x : Site k) (d : Nat) : Option (Site k) :=
  let i : Int := x.1.val
  let j : Int := x.2.val
  let u := i+(if d=1 then 1 else if d=3 then -1 else 0)
  let v := j+(if d=0 then 1 else if d=2 then -1 else 0)
  if h : 0≤u ∧ 0≤v ∧ u.toNat<N k ∧ v.toNat<N k then
    some (⟨u.toNat,h.2.2.1⟩,⟨v.toNat,h.2.2.2⟩) else none

def neighbor (F : Finset (Site k)) (x : Site k) (d : Nat) :=
  ((probe x d).map (fun y => (decide (y∈F)).toNat)).getD 9

/-- `out=none` is a root. Arrows are read from a single physical
orientation; reflection changes the arrow as well as its four neighbors. -/
def starCode (n i j : Nat) (nb : Nat → Nat) (out : Option (Fin 4)) :=
  minimum fun g =>
    let p := transform g n i j
    pack (fine n 8 p.1 p.2 ++ (List.range 4).map (fun d => nb (direction (invers g) d)) ++
      [(out.map (fun d => direction g d.val+1)).getD 0])

def star (F : Finset (Site k)) (out : Site k → Option (Fin 4)) (x : Site k) :=
  8*starCode (N k) x.1.val x.2.val (neighbor F x) (out x)+(decide (x∈F)).toNat

def small (n : Nat) [NeZero n] (g : Fin 8) (x : Fin n × Fin n) : Fin n × Fin n :=
  let p := transform g n x.1.val x.2.val
  (Fin.ofNat n p.1,Fin.ofNat n p.2)

def rotatedMask (m : Mask) (g : Fin 8) :=
  (List.range 16).foldl (fun a t =>
    let p := small 4 (invers g) (Fin.ofNat 4 (t/4),Fin.ofNat 4 t)
    a + (m p.1 p.2).toNat*2^t) 0

def partition (q : PartitionBits) (g : Fin 8) :=
  let c (i : Nat) := small 2 (invers g) (Fin.ofNat 2 (i/2),Fin.ofNat 2 i)
  let first (i : Nat) := ((List.range (i+1)).find? (fun j => q (c j) (c i))).getD i
  (List.range 4).foldl (fun a i => 4*a+((List.range (first i)).filter (fun j => first j==j)).length) 0

def faceViews (mask : Mask) (q : PartitionBits) : Vector Nat 8 :=
  Vector.ofFn fun g => rotatedMask mask g*256+partition q g

def keyAt (p : FacePos k) (v : Vector Nat 8) :=
  8*(minimum fun g =>
    let t := transform g (N k-3) (3*p.1.val) (3*p.2.val)
    pack [axis (N k-3) 2 t.1,axis (N k-3) 2 t.2]*16777216+v[g])+2

def faceCode (p : FacePos k) (mask : Mask) (q : PartitionBits) := keyAt p (faceViews mask q)

noncomputable def face (F : Finset (Site k)) (p : FacePos k) :=
  faceCode p (faceAtom F p).1 (faceAtom F p).2

def state (s : State) :=
  let m := match s.mode with | .pre => 0 | .on => 1 | .gap => 2 | .p0 => 3 | .p1 => 4
  (m*9+(s.prev.map (fun a => 1+4*a.l.toNat+2*a.z.toNat+a.r.toNat)).getD 0)*2+s.hit.toNat

instance : NeZero (N k) := ⟨by unfold N; omega⟩
def view (F : Finset (Site k)) (g : Fin 8) :=
  F.image (small (N k) g)

def line (F : Finset (Site k)) (g : Fin 8) (row slot : Fin (k+1)) :=
  let S := view F g
  let v := teeth k row
  let j := slot.val
  let prev := if j=0 then 0 else axis (N k) 8 (3*j-3)+1
  8*((pack [axis (N k) 8 v.val,prev,axis (N k) 8 (3*j)]*90+
    state (prefixState S v j))*90+state (prefixState S v (j+1)))+3

abbrev PatchPos (k : Nat) := Fin (N k-2) × Fin (N k-2)
abbrev Nine := Fin 3 × Fin 3 → Bool
def patchCode (p : PatchPos k) (a : Nine) :=
  8*(minimum fun g =>
    let t := transform g (N k-2) p.1.val p.2.val
    let mask := (List.range 9).foldl (fun m j =>
      let q := small 3 (invers g) (Fin.ofNat 3 (j/3),Fin.ofNat 3 j)
      m+(a q).toNat*2^j) 0
    pack (fine (N k-2) 7 t.1 t.2)*512+mask)+4

def patchMask (F : Finset (Site k)) (p : PatchPos k) : Nine := fun q =>
  let i := Fin.ofNat (N k) (p.1.val+q.1.val)
  let c := Fin.ofNat (N k) (p.2.val+q.2.val)
  decide ((i,c)∈F)
def patch (F : Finset (Site k)) (p : PatchPos k) := patchCode p (patchMask F p)

/-- Minimal nonnegative auxiliary count in a pooled nonjunction row
band, using marks on tooth columns in all eight square views. -/
def complete (F : Finset (Site k)) (band : Nat) : Int :=
  let rows := Finset.univ.filter fun r : Fin (N k) => axis (N k) 8 r.val=band ∧ r.val%3≠0
  max 0 (∑ g : Fin 8, ∑ r ∈ rows,
    (((Finset.univ.filter fun j : Fin (k+1) => (r,teeth k j)∈view F g).card:Int)-k))

end GridGraphs.NoPitch.Keys
