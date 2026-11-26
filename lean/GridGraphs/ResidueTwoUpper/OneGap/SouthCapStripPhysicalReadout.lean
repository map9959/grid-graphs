import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripGridGraph

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 Camera FanSeed SimpleGraph
namespace GridScan

theorem offsets_fit {h : Nat} (s : Window h (width h)) (k used : Nat) {p : Pos}
    (inside : (prefixBox s k used).Contains p) :
    let B := prefixBox s k used
    (0≤alongOffset s.axis B p ∧ alongOffset s.axis B p<used) ∧
      0≤acrossOffset s.axis B p ∧ acrossOffset s.axis B p<3*(s.depth:Int) := by
  cases dir : s.axis <;>
    simp [prefixBox,dir,SiteBox.Contains,alongOffset,acrossOffset] at inside ⊢ <;> omega

theorem scanPoint_inverse (axis : Axis) (B : SiteBox) (p : Pos)
    (a : 0≤alongOffset axis B p) (b : 0≤acrossOffset axis B p) :
    scanPoint B axis (alongOffset axis B p).toNat (acrossOffset axis B p).toNat=p := by
  cases axis <;>
    simp only [scanPoint,alongOffset,acrossOffset] at a b ⊢ <;>
    apply Prod.ext <;>
    simp only [Int.toNat_of_nonneg a,Int.toNat_of_nonneg b] <;> omega

def vertexOf {u h : Nat} (s : Window h (width h)) (v : View) (used : Nat)
    (x : (prefixBox s (11+14*u) used).vertices (n:=35+42*u) v) : Vertex (3*s.depth) :=
  let B := prefixBox s (11+14*u) used
  let p := coordinates v x.val
  let bounds := offsets_fit s (11+14*u) used x.2
  site ((alongOffset s.axis B p).toNat+1)
    ⟨(acrossOffset s.axis B p).toNat,by
      have q : acrossOffset s.axis B p<3*(s.depth:Int) := bounds.2.2
      omega⟩

theorem vertexOf_shape {u h : Nat} (s : Window h (width h)) (v : View) (used : Nat)
    (x : (prefixBox s (11+14*u) used).vertices (n:=35+42*u) v) :
    ∃ (j : Nat) (i : Fin (3*s.depth)), j<used ∧ vertexOf s v used x=site (j+1) i ∧
      scanPoint (prefixBox s (11+14*u) used) s.axis j i=coordinates v x.val ∧
      alongOffset s.axis (prefixBox s (11+14*u) used) (coordinates v x.val)=j ∧
      acrossOffset s.axis (prefixBox s (11+14*u) used) (coordinates v x.val)=i.val := by
  have fit := offsets_fit s (11+14*u) used x.2
  dsimp only at fit
  refine ⟨_,_,?_,rfl,scanPoint_inverse s.axis _ _ fit.1.1 fit.2.1,?_,?_⟩
  · have h := fit.1.2
    omega
  · exact (Int.toNat_of_nonneg fit.1.1).symm
  · exact (Int.toNat_of_nonneg fit.2.1).symm

theorem vertexOf_mark {u h : Nat} (s : Window h (width h)) (F : Finset (Site u))
    (v : View) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length)
    (x : (prefixBox s (11+14*u) used).vertices v) :
    Mark (physicalProgram s F v north) (vertexOf s v used x) ↔ x.val∈F := by
  obtain ⟨j,i,jl,eq,read,_,_⟩ := vertexOf_shape s v used x
  rw [eq]
  change (physicalProgram s F v north).mark j i=true ↔ x.val∈F
  rw [physical_program_mark s F v north hk lo hi j i (by omega),
    scanPoint_prefix s (11+14*u) (3*s.length) used,read]
  have pt : point u v (coordinates v x.val)=x.val := by
    apply point_inj v
    have on := scanPoint_board s hk lo hi size jl i.isLt
    rw [read] at on
    exact coords_point on
  rw [pt]

theorem vertexOf_surj {u h : Nat} (s : Window h (width h)) (v : View)
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used j : Nat) (size : used≤3*s.length) (jl : j<used) (i : Fin (3*s.depth)) :
    ∃ a : (prefixBox s (11+14*u) used).vertices (n:=35+42*u) v,
      vertexOf s v used a=site (j+1) i := by
  let p := scanPoint (prefixBox s (11+14*u) used) s.axis j i
  let x := point u v p
  have px : coordinates v x=p := coords_point (scanPoint_board s hk lo hi size jl i.isLt)
  have inside : (prefixBox s (11+14*u) used).Contains (coordinates v x) := by
    rw [px]
    exact (scanPoint_contains s _ used j i).mpr ⟨jl,i.isLt⟩
  refine ⟨⟨x,inside⟩,?_⟩
  obtain ⟨k,b,_,read,_,along,across⟩ := vertexOf_shape s v used ⟨x,inside⟩
  change alongOffset s.axis (prefixBox s (11+14*u) used) (coordinates v x)=k at along
  change acrossOffset s.axis (prefixBox s (11+14*u) used) (coordinates v x)=b.val at across
  have offsets := scanPoint_offsets s (11+14*u) used j i
  rw [px,offsets.1] at along
  rw [px,offsets.2] at across
  rw [read,show k=j by omega,show b=i from Fin.ext (by omega)]

theorem vertexOf_adj {u h : Nat} (s : Window h (width h)) (F : Finset (Site u))
    (v : View) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (used : Nat) (size : used≤3*s.length)
    (a b : (prefixBox s (11+14*u) used).vertices v)
    (edge : (Bonds F).Adj a.val b.val) :
    (graph (physicalProgram s F v north) used).Adj (vertexOf s v used a) (vertexOf s v used b) := by
  obtain ⟨j,i,jl,eq,read,_,_⟩ := vertexOf_shape s v used a
  obtain ⟨k,t,kl,eq',read',_,_⟩ := vertexOf_shape s v used b
  have A := vertexOf_mark s F v north hk lo hi used size a
  have B := vertexOf_mark s F v north hk lo hi used size b
  rw [eq] at A
  rw [eq'] at B
  rw [eq,eq',graph_adj_sites]
  refine ⟨by omega,by omega,by omega,by omega,?_,?_⟩
  · have metric := (Camera.adj_iff v _ _).mp edge.1
    rw [←read,←read'] at metric
    rw [lattice_metric]
    cases ax : s.axis <;> simpa [scanPoint,ax, abs_sub_comm,add_comm] using metric
  · exact edge.2.imp A.mpr B.mpr

theorem graph_reachable_bounded {n : Nat} (p : Row.Program n) (used : Nat)
    {x y : Vertex n} (xl : level x≤used) (reach : (graph p used).Reachable x y) :
    level y≤used := by
  obtain ⟨w⟩ := reach
  have r := w.reverse
  cases r with
  | nil => exact xl
  | cons edge _ =>
    obtain ⟨j,lt,k,_,eq⟩ := (graph_edges p used _).mp ((mem_edgeSet _).mpr edge)
    have h := namedEdge_grade j k
    rw [eq,grade_mk] at h
    omega

/-- Exact readout of any consumed physical prefix. The root wire is
read at the same indexed vertex as the associated marked rim site. -/
def prefixReadout {u h : Nat} (s : Window h (width h)) (F : Finset (Site u))
    (v : View) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (j : Nat) (size : j+1≤3*s.length) :
    let p := physicalProgram s F v north
    PrefixReadout (F:=F) (v:=v) s (j+1) (graph p (j+1)) (slots (3*s.depth) j) (Mark p) (Open p) := by
  let p := physicalProgram s F v north
  let used := j+1
  let B := prefixBox s (11+14*u) used
  let n := 3*s.depth
  refine ⟨vertexOf s v used,?_,?_,?_,?_,?_⟩
  · intro a b reach
    let f : ((Bonds F).induce (B.vertices v)) →g graph p used :=
      ⟨vertexOf s v used,fun e => vertexOf_adj s F v north hk lo hi used size _ _ e⟩
    exact reach.map f
  · intro x hx z reach mk
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    have le : level (slots n j (Row.oldSlot i.castSucc))≤used := by simp [level,site,used]
    have zle := graph_reachable_bounded p used le reach
    cases z with
    | none => exact False.elim mk
    | some z =>
      obtain ⟨k,b⟩ := z
      cases k with
      | zero => exact False.elim mk
      | succ k =>
        change k+1≤used at zle
        obtain ⟨a,read⟩ := vertexOf_surj s v hk lo hi used k size (by omega) b
        have ha := (vertexOf_mark s F v north hk lo hi used size a).mp (read.symm ▸ mk)
        exact ⟨a,ha,read⟩
  · intro a
    obtain ⟨k,i,_,atSite,_,aOff,bOff⟩ := vertexOf_shape s v used a
    dsimp only
    intro open'
    rw [aOff,bOff] at open'
    refine ⟨_,Reachable.rfl,?_⟩
    rw [atSite]
    exact decide_eq_true open'
  · intro a
    obtain ⟨k,i,_,atSite,_,aOff,_⟩ := vertexOf_shape s v used a
    dsimp only
    intro _ onFront
    rw [aOff] at onFront
    have eq : k=j := by change (k:Int)+1=(j+1:Nat) at onFront; omega
    refine ⟨i.castSucc,?_⟩
    simp [Row.keep,atSite,eq]
  · intro a
    obtain ⟨k,i,kl,atSite,_,aOff,bOff⟩ := vertexOf_shape s v used a
    dsimp only
    intro marked wire
    rw [aOff,bOff] at wire
    have am := (vertexOf_mark s F v north hk lo hi used size a).mpr marked
    rw [atSite] at am
    refine ⟨none,?_,trivial⟩
    rw [atSite]
    apply Adj.reachable
    apply (graph_adj_root p used (k+1) i).mpr
    exact ⟨by omega,by omega,am,by simp [physicalProgram,wire,p]⟩

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
