import GridGraphs.ResidueTwoUpper.OneGap.FanEast

/-! A label is a whole physical tile and its twelve outgoing edge bits.
Only restrictions of the direction field on nine sites are enumerated.
The window may leak at either lateral boundary. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
open FanSlab L7

def shapes := [9,72,73,2,66,16,128,129,132,36,258,288,292]
def clash (m i j d e f : Nat) := ((d==f) != (e==(f+2)%4)) == (m.testBit i || m.testBit j) && !(d==f && e==(f+2)%4)
-- i is visited after its western and northern neighbors.
def tileOK (m i old d : Nat) := (i%3==0 || clash m i (i-1) d ((old >>> (2*(i-1)))%4) 2) &&
  (i<3 || clash m i (i-3) d ((old >>> (2*(i-3)))%4) 3)
def contrib (i d : Nat) := if (d==0 && i%3==2) || (d==1 && i/3==2) || (d==2 && i%3==0) || (d==3 && i/3==0) then
  1 <<< (3*d+(if d%2=0 then i/3 else i%3)) else 0
private def paths (m : Nat) : Nat → List (Nat × Nat)
  | 0 => [(0,0)]
  | i+1 => (paths m i).flatMap fun (o,b) => ((List.range 4).filter (tileOK m i o)).map fun d => (o+(d <<< (2*i)),b+contrib i d)
def labels (m : Nat) := ((paths m 9).map fun p => (m <<< 12)+p.2).eraseDups
def mask (l : Nat) := l >>> 12
def out (l d : Nat) := (l >>> (3*d))%8
def edge (m d : Nat) := ((List.range 3).map fun j => (m.testBit (if d=0 then 3*j+2 else if d=1 then 6+j else if d=2 then 3*j else j)).toNat <<< j).sum
def meets (d a b : Nat) := let e := d+2; let s := out a d; let t := out b e
  (s &&& t)==0 && (s ||| t)==(edge (mask a) d ||| edge (mask b) e)

def corner (a b c d r s : Nat) := bits fun k : Fin 9 =>
  let y := r+k.val/3; let x := s+k.val%3
  (if x<3 then (if y<3 then a else b) else (if y<3 then c else d)).testBit (3*(y%3)+x%3)
def markOK (a b c d : Nat) := (a != 73 || c==73) && (b != 73 || d==73) &&
  (List.range 4).all fun r => (List.range 4).all fun s => accepts (5+(r+1)%3) (5+(s+1)%3) (corner a b c d r s)

structure Quad where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving Inhabited, BEq, DecidableEq

def poolWith (ad : Nat → Nat → Nat → Nat → Bool) (ws : List (Nat × List Nat)) := ws.flatMap fun (a,A) => ws.flatMap fun (b,B) =>
  ws.flatMap fun (c,C) => ws.flatMap fun (d,D) => if !ad a b c d then [] else
    A.flatMap fun x => (B.filter (meets 1 x)).flatMap fun y => (C.filter (meets 0 x)).flatMap fun z =>
      (D.filter fun t => meets 0 y t && meets 1 z t).map fun t => Quad.mk x y z t
def master := poolWith markOK (shapes.map fun m => (m,labels m))

theorem in_pool (ad : Nat → Nat → Nat → Nat → Bool) {a b c d x y z t} (ha : a∈shapes) (hb : b∈shapes) (hc : c∈shapes) (hd : d∈shapes)
    (xa : x∈labels a) (yb : y∈labels b) (zc : z∈labels c) (td : t∈labels d)
    (ok : ad a b c d) (xy : meets 1 x y) (xz : meets 0 x z) (yt : meets 0 y t) (zt : meets 1 z t) :
    Quad.mk x y z t∈poolWith ad (shapes.map fun m => (m,labels m)) := by
  let ws := shapes.map fun m => (m,labels m)
  have mem (m) (h : m∈shapes) : (m,labels m)∈ws := List.mem_map.mpr ⟨m,h,rfl⟩
  apply List.mem_flatMap.mpr; refine ⟨_,mem _ ha,?_⟩
  apply List.mem_flatMap.mpr; refine ⟨_,mem _ hb,?_⟩
  apply List.mem_flatMap.mpr; refine ⟨_,mem _ hc,?_⟩
  apply List.mem_flatMap.mpr; refine ⟨_,mem _ hd,?_⟩
  simp only [ok,Bool.not_true,Bool.false_eq_true,if_false]
  exact List.mem_flatMap.mpr ⟨_,xa,List.mem_flatMap.mpr ⟨_,List.mem_filter.mpr ⟨yb,xy⟩,List.mem_flatMap.mpr
    ⟨_,List.mem_filter.mpr ⟨zc,xz⟩,List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨td,by simp [yt,zt]⟩,rfl⟩⟩⟩⟩

theorem in_master {a b c d x y z t} (ha : a∈shapes) (hb : b∈shapes) (hc : c∈shapes) (hd : d∈shapes)
    (xa : x∈labels a) (yb : y∈labels b) (zc : z∈labels c) (td : t∈labels d)
    (ok : markOK a b c d) (xy : meets 1 x y) (xz : meets 0 x z) (yt : meets 0 y t) (zt : meets 1 z t) :
    Quad.mk x y z t∈master := in_pool markOK ha hb hc hd xa yb zc td ok xy xz yt zt

def field (D : Nat → Nat) : Nat → Nat × Nat
  | 0 => (0,0)
  | i+1 => let (o,b) := field D i; (o+(D i <<< (2*i)),b+contrib i (D i))
theorem real_label (m : Nat) (D : Nat → Nat) (bound : ∀ i<9, D i<4) (check : ∀ i<9, tileOK m i (field D i).1 (D i)) :
    (m <<< 12)+(field D 9).2∈labels m := by
  have go (i : Nat) (hi : i≤9) : field D i∈paths m i := by
    induction i with
    | zero => simp [paths,field]
    | succ i ih => exact List.mem_flatMap.mpr ⟨_,ih (by omega),List.mem_map.mpr ⟨_,List.mem_filter.mpr
        ⟨List.mem_range.mpr (bound i (by omega)),check i (by omega)⟩,rfl⟩⟩
  exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨_,go 9 le_rfl,rfl⟩)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
