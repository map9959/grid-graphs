import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripGridGraph

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open SimpleGraph

/-- A north-attached rail must escape the eastern column. This only
reads three sites per tile. If its top-left site is marked then a
marked neighbor to the right gives an east attachment. Alternatively
a marked neighbor below carries the path to the next tile (the gap
of one unmarked site is bridged by the next marked top-left site).
At the last tile that same neighbor gives a south attachment. -/
theorem eastRail_obstruction (h : Nat) (height : 2≤h) (p : Row.Program 6)
    (acy : (graph p (3*h)).IsAcyclic)
    (north : p.mark 1 3=true ∧ p.tooth 1 3=true)
    (east : ∀ k<h, p.tooth (3*k) 4=true)
    (south : p.tooth (3*(h-1)+1) 3=true)
    (head : ∀ k<h, p.mark (3*k) 3=true)
    (carry : ∀ k<h, p.mark (3*k) 4=true ∨ p.mark (3*k+1) 3=true) : False := by
  let G := graph p (3*h)
  let top : Vertex 6 := site 2 3
  let D := G.deleteEdges {s(top,none)}
  have wire {j : Nat} {i : Fin 6} (jl : j<3*h)
      (m : p.mark j i=true) (t : p.tooth j i=true) : G.Adj (site (j+1) i) none :=
    (graph_adj_root ..).mpr ⟨by omega,by omega,m,t⟩
  have forbidden : ¬D.Reachable top none :=
    isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp acy
      (wire (j:=1) (by omega) north.1 north.2))
  have inner {j k : Nat} {a b : Fin 6} (jl : j<3*h) (kl : k<3*h)
      (near : lattice (j+1) (k+1) a b) (m : p.mark j a=true ∨ p.mark k b=true) :
      D.Reachable (site (j+1) a) (site (k+1) b) := by
    apply Adj.reachable
    apply (deleteEdges_adj ..).mpr
    refine ⟨(graph_adj_sites ..).mpr ⟨by omega,by omega,by omega,by omega,near,m⟩,?_⟩
    simp [site,top]
  have other {j : Nat} {i : Fin 6} (jl : j<3*h) (ne : site (j+1) i≠top)
      (m : p.mark j i=true) (t : p.tooth j i=true) : D.Reachable (site (j+1) i) none := by
    apply Adj.reachable
    apply (deleteEdges_adj ..).mpr
    exact ⟨wire jl m t,by simp [site] at *; assumption⟩
  have reach (k : Nat) (kl : k<h) : D.Reachable top (site (3*k+1) 3) := by
    induction k with
    | zero =>
      exact inner (j:=1) (k:=0) (by omega) (by omega) (.inl ⟨.inr rfl,rfl⟩) (.inl north.1)
    | succ k ih =>
      have hk : k<h := by omega
      have old := ih hk
      rcases carry k hk with side|down
      · have turn := inner (j:=3*k) (k:=3*k) (a:=3) (b:=4) (by omega) (by omega)
          (.inr ⟨rfl,.inl rfl⟩) (.inr side)
        have ne : site (3*k+1) (4 : Fin 6)≠top := by simp [site,top,Fin.ext_iff]
        exact (forbidden ((old.trans turn).trans (other (by omega) ne side (east k hk)))).elim
      · have vert (j : Nat) (jl : j+1<3*h)
            (m : p.mark j 3=true ∨ p.mark (j+1) 3=true) :=
          inner (j:=j) (k:=j+1) (by omega) jl (.inl ⟨.inl rfl,rfl⟩) m
        have endMark := head (k+1) kl
        rw [show 3*(k+1)=3*k+2+1 by omega] at endMark ⊢
        exact (((old.trans (vert _ (by omega) (.inr down))).trans
          (vert _ (by omega) (.inl down))).trans (vert _ (by omega) (.inr endMark)))
  let k := h-1
  have hk : k<h := by dsimp [k]; omega
  have hit := reach k hk
  rcases carry k hk with side|down
  · have turn := inner (j:=3*k) (k:=3*k) (a:=3) (b:=4) (by omega) (by omega)
        (.inr ⟨rfl,.inl rfl⟩) (.inr side)
    exact forbidden ((hit.trans turn).trans (other (by omega)
      (by simp [site,top,Fin.ext_iff]) side (east k hk)))
  · have turn := inner (j:=3*k) (k:=3*k+1) (a:=3) (b:=3) (by omega) (by omega)
        (.inl ⟨.inl rfl,rfl⟩) (.inr down)
    exact forbidden ((hit.trans turn).trans (other (by omega)
      (by simp [site,top,k]; omega) down south))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
