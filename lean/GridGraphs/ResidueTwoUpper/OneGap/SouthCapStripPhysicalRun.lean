import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripPhysicalAcyclic

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph ResidueZero L7 BoundarySix.Connected
namespace GridScan

theorem final_components_open {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (s : Window h (width h)) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (j : Nat) (finished : j+1=3*s.length) :
    let p := physicalProgram s F v north
    ∀ i, ComponentFlag (graph p (j+1)) (Mark p) (frontier (3*s.depth) (j+1) i) →
      ComponentFlag (graph p (j+1)) (Open p) (frontier (3*s.depth) (j+1) i) := by
  let p := physicalProgram s F v north
  let used := j+1
  let Q := graph p used
  let read := prefixReadout s F v north hk lo hi j (le_of_eq finished)
  dsimp only
  intro i
  rintro ⟨z,hit,mz⟩
  have bound : level (frontier (3*s.depth) used i)≤used := by
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [site,level]
  have zle := graph_reachable_bounded p used bound hit
  cases z with
  | none => exact False.elim mz
  | some z =>
    obtain ⟨k,b⟩ := z
    cases k with
    | zero => exact False.elim mz
    | succ k =>
      change k+1≤used at zle
      obtain ⟨a,az⟩ := vertexOf_surj s v hk lo hi used k (le_of_eq finished) (by omega) b
      have ma := (vertexOf_mark s F v north hk lo hi used (le_of_eq finished) a).mp (az.symm ▸ mz)
      obtain ⟨b,ab,good⟩ := cap_prefix_flags H acy score s hk lo hi used (le_of_eq finished) a ma
      have via := read.reach a b ab
      change Q.Reachable (vertexOf s v used a) (read.point b) at via
      rw [az] at via
      have open' : ComponentFlag Q (Open p) (read.point b) := by
        rcases good with o|⟨unfinished,_⟩|⟨mb,w⟩
        · exact read.openFlag b o
        · exact (Nat.lt_irrefl _ (finished ▸ unfinished)).elim
        · exact read.wiredFlag b mb w
      obtain ⟨y,by',flag⟩ := open'
      exact ⟨y,hit.trans (via.trans by'),flag⟩

theorem physical_run_prefix {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2)
    (s : Window h (width h)) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : FanSlab.square F v (firstRow (11+14*u) h) (1+3*(11+14*u-1))=73)
    (size : 3*s.depth+1≤16) (j : Nat) (bound : j≤3*s.length) :
    ∃ t, (physicalProgram s F v north).run (Row.basePartition (3*s.depth)).pack j=some t := by
  let p := physicalProgram s F v north
  let n := 3*s.depth
  have close (i : Nat) (il : i<3*s.length) :
      RowClosure (graph p (i+1)) (slots n i) (Mark p) (Open p) (Row.drop n) Row.keep :=
    physical_row_closure H acy score s hk lo hi (i+1) (by omega)
      (prefixReadout s F v north hk lo hi i (by omega))
  let z := realization p (3*s.length) close
  obtain ⟨t,eq,_⟩ := Row.packed_run_reflects z
    (physical_graph_acyclic H acy one s north hk lo hi line top) size (grid_base_reflects p size) j bound
  exact ⟨t,eq⟩

/-- The packed forest machine accepts every physical horizontal or
vertical cap strip of supported transverse width. This is an actual
run on physical marks and the exact indexed edge schedule, not a
premise that physical traces exist. -/
theorem physical_packed_run_accepts {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2)
    (s : Window h (width h)) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : FanSlab.square F v (firstRow (11+14*u) h) (1+3*(11+14*u-1))=73)
    (size : 3*s.depth+1≤16) :
    let p := physicalProgram s F v north
    ∃ t, p.run (Row.basePartition (3*s.depth)).pack (3*s.length)=some t ∧
      Row.Program.accepts (3*s.depth) t=true := by
  let p := physicalProgram s F v north
  have forest := physical_graph_acyclic H acy one s north hk lo hi line top
  apply run_grid_accepts p size forest
  · intro j jl
    have size' : j+1≤3*s.length := by omega
    exact physical_row_closure H acy score s hk lo hi (j+1) size'
      (prefixReadout s F v north hk lo hi j size')
  · have nonzero : 3*s.length≠0 := by
      cases ax : s.axis <;> simp [Window.length,ax,width]
      all_goals omega
    obtain ⟨j,eq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
    have last := final_components_open H acy score s north hk lo hi j eq.symm
    rw [eq]
    exact last

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
