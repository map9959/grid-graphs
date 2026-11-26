import GridGraphs.NoPitch.TailRows.IncidenceGeometry
import GridGraphs.NoPitch.TailRows.IncidenceTags58
import GridGraphs.NoPitch.TailRows.IncidenceTags61

namespace GridGraphs.NoPitch.TailRows.Incidence
open PitchCut Keys LocalBoard19 FaceRows GridGraphs.NoPitch.Dual Budget

def validAxis (h a : Nat) (u dn : Int) :=
  decide ((a:Int)+u≥0 ∧ (a:Int)+u-dn<2*h+3)
def valid (h : Nat) (v : List Nat) (r c dn : Int) :=
  validAxis h v[0]! r dn && validAxis h v[1]! c dn
def eventKey (x y : List Nat) (d : Nat) := pack (x++y++[d])*64
def lookup (T : Table) (key : Option Nat) (word : Nat) : Terms :=
  match key with | none => [] | some v => T[v+word]?.getD []
def port (h : Nat) (v : List Nat) (z : Fin 4) : Option Nat :=
  if valid h v (dr z) (dc z) 0 then
    let a := moved h v 0 0 0
    let b := moved h v (dr z) (dc z) 0
    some (if z.val<2 then eventKey a b z.val else eventKey b a (z.val-2))
  else none
def socket (v : List Nat) (z : Q) : Option Nat :=
  if valid 8 v (-(z.1.val:Int)) (-(z.2.val:Int)) (-2) then
    some (eventKey (moved 8 v (-(z.1.val:Int)) (-(z.2.val:Int)) (-2)) (moved 8 v 0 0 0) (3*z.1.val+z.2.val))
  else none
def plug (v : List Nat) (z : Q) : Option Nat :=
  some (eventKey (moved 7 v 0 0 0) (moved 7 v z.1.val z.2.val 2) (3*z.1.val+z.2.val))

structure Book where
  start : Nat
  cells : Nat
  pairs : Nat
  stop : Nat
  E : Table
  S : Table
  P : Table
def book58 := Book.mk edgeStart58 cellStart58 pairStart58 (pairStart58+pairTags58.size)
  (tagMap edgeTags58 edgeStart58) (tagMap cellTags58 cellStart58) (tagMap pairTags58 pairStart58)
def book61 := Book.mk edgeStart61 cellStart61 pairStart61 (pairStart61+pairTags61.size)
  (tagMap edgeTags61 edgeStart61) (tagMap cellTags61 cellStart61) (tagMap pairTags61 pairStart61)
def Book.sel (B : Book) (i : Nat) := B.start ≤ i && i < B.stop

abbrev Views := Fin 8 → List Nat
def edgeAt (B : Book) (v : Views) (d : Fin 4) (g : Fin 8) (f b a : Bool) : Terms :=
  let z := dirView g d
  let key := port 8 (v g) z
  if z.val<2 then lookup B.E key (edgeWord f b a) else negTerms (lookup B.E key (edgeWord b f (!a)))
def pairAt (B : Book) (v : Views) (d : Fin 4) (g : Fin 8) (a : Nine) : Terms :=
  let z := dirView g d
  let ts := lookup B.P (port 7 (v g) z) (word6 a g z)
  if z.val<2 then ts else negTerms ts
def socketAt (B : Book) (v : Views) (q : Q) (g : Fin 8) (f : Bool) (bits : Fin 4 → Bool) :=
  let z := small 3 g q
  lookup B.S (socket (v g) z) (cellWord z f (rotatedBits bits g))
def plugAt (B : Book) (v : Views) (q : Q) (g : Fin 8) (a : Nine) :=
  let z := small 3 g q
  lookup B.S (plug (v g) z) (cellWord z (a q) (patchBits a q g))

def stampStar (B : Book) (v : Views) (f : Bool) (bits : Fin 4 → Bool) (o : Option (Fin 4)) :=
  ((List.finRange 4).flatMap fun d => viewSum fun g => edgeAt B v d g f (bits d) (o==some d)) ++
  (offsets.flatMap fun q => viewSum fun g => socketAt B v q g f bits)
def stampPatch (B : Book) (v : Views) (a : Nine) :=
  ((List.finRange 4).flatMap fun d => viewSum fun g => pairAt B v d g a) ++
  negTerms (offsets.flatMap fun q => viewSum fun g => plugAt B v q g a)

/-- Precompute the position-dependent keys once per representative.
The resulting closures are shared across the local state enumeration. -/
def starCheck {b} (w : Nat → Terms) (B : Book) (x : Site b) :=
  let v := starFine x
  let edges := Vector.ofFn fun d => Vector.ofFn fun g => port 8 (v g) (dirView g d)
  let cells := Vector.ofFn fun (u : Fin 3) => Vector.ofFn fun (t : Fin 3) =>
    Vector.ofFn fun g => socket (v g) (small 3 g (u,t))
  decide (∀ bits f o, admissible x bits f o →
    let e := (List.finRange 4).flatMap fun d => viewSum fun g =>
      let z := dirView g d; let a := o==some d; let key := edges[d][g]
      if z.val<2 then lookup B.E key (edgeWord f (bits d) a)
      else negTerms (lookup B.E key (edgeWord (bits d) f (!a)))
    let s := offsets.flatMap fun q => viewSum fun g =>
      lookup B.S cells[q.1][q.2][g] (cellWord (small 3 g q) f (rotatedBits bits g))
    balanced (w (sKey x f bits o) ++ negTerms (e++s)))

def patchCheck {b} (w : Nat → Terms) (B : Book) (p : PatchPos b) :=
  let v := patchFine p
  let pairs := Vector.ofFn fun d => Vector.ofFn fun g => port 7 (v g) (dirView g d)
  let cells := Vector.ofFn fun (u : Fin 3) => Vector.ofFn fun (t : Fin 3) =>
    Vector.ofFn fun g => plug (v g) (small 3 g (u,t))
  decide (∀ a, legal a →
    let e := (List.finRange 4).flatMap fun d => viewSum fun g =>
      let z := dirView g d
      let ts := lookup B.P pairs[d][g] (word6 a g z)
      if z.val<2 then ts else negTerms ts
    let s := offsets.flatMap fun q => viewSum fun g =>
      lookup B.S cells[q.1][q.2][g] (cellWord (small 3 g q) (a q) (patchBits a q g))
    balanced (w (patchCode p a) ++ negTerms (e++negTerms s)))

def cert (D : Chart) (B : Book) (b : Nat) :=
  let w := contribution D (index D) (prices D B.sel)
  supported D B.sel && decide (∀ x : Site b, starCheck w B x) && decide (∀ p : PatchPos b, patchCheck w B p)

end GridGraphs.NoPitch.TailRows.Incidence
