import GridGraphs.GridDirection
import GridGraphs.PermutationCut
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# The contour permutation of an embedded grid tree

The clockwise local rotations define a permutation of directed tree edges.  A
tree edge is a bridge, so deleting it splits the vertices into two shores.  The
two orientations of that edge are the unique exit and entry of the associated
dart shore; finite permutation cut balance therefore places them in one contour
orbit.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

set_option maxHeartbeats 800000

namespace GridDirectionalDart

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- The unordered tree edge underlying a directional dart. -/
def edgeSym2 (d : GridDirectionalDart T) : Sym2 (GridVertex m n) :=
  s(d.source, d.target)

/-- Vertices on the target side after deleting the dart's tree edge. -/
noncomputable def targetShoreVertices (d : GridDirectionalDart T) :
    Finset (GridVertex m n) :=
  Finset.univ.filter fun v =>
    (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable
      d.target v

/-- Contour states whose source lies on the target shore. -/
noncomputable def targetShoreDarts (d : GridDirectionalDart T) :
    Finset (GridDirectionalDart T) :=
  Finset.univ.filter fun x => x.source ∈ d.targetShoreVertices

@[simp] theorem mem_targetShoreVertices (d : GridDirectionalDart T)
    (v : GridVertex m n) :
    v ∈ d.targetShoreVertices ↔
      (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable
        d.target v := by
  simp [targetShoreVertices]

@[simp] theorem mem_targetShoreDarts (d x : GridDirectionalDart T) :
    x ∈ d.targetShoreDarts ↔ x.source ∈ d.targetShoreVertices := by
  simp [targetShoreDarts]

theorem target_mem_targetShoreVertices (d : GridDirectionalDart T) :
    d.target ∈ d.targetShoreVertices := by
  rw [mem_targetShoreVertices]

theorem source_notMem_targetShoreVertices
    (hacyc : T.IsAcyclic) (d : GridDirectionalDart T) :
    d.source ∉ d.targetShoreVertices := by
  rw [mem_targetShoreVertices]
  have hbridge : T.IsBridge d.edgeSym2 := by
    rw [SimpleGraph.isAcyclic_iff_forall_isBridge] at hacyc
    apply hacyc
    change s(d.source, d.target) ∈ T.edgeSet
    rw [SimpleGraph.mem_edgeSet]
    exact d.adj
  intro hreach
  exact hbridge hreach.symm

/-- Every tree edge crossing a fundamental shore is its attachment edge. -/
theorem edgeSym2_eq_of_source_mem_target_notMem (d x : GridDirectionalDart T)
    (hxIn : x.source ∈ d.targetShoreVertices)
    (hxOut : x.target ∉ d.targetShoreVertices) :
    x.edgeSym2 = d.edgeSym2 := by
  by_contra hne
  have hxReach :
      (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Reachable
        d.target x.source := by
    simpa only [mem_targetShoreVertices] using hxIn
  have hxAdj :
      (T.deleteEdges ({d.edgeSym2} : Set (Sym2 (GridVertex m n)))).Adj
        x.source x.target := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨x.adj, by simpa [edgeSym2] using hne⟩
  have hxTarget := hxReach.trans hxAdj.reachable
  exact hxOut (by simpa only [mem_targetShoreVertices] using hxTarget)

/-- The reverse dart is the unique contour state leaving the target shore. -/
theorem eq_reverse_of_mem_targetShore_of_contourSucc_notMem
    (hacyc : T.IsAcyclic) (d x : GridDirectionalDart T)
    (hxIn : x ∈ d.targetShoreDarts)
    (hxOut : x.contourSucc ∉ d.targetShoreDarts) :
    x = d.reverse := by
  have hxSource : x.source ∈ d.targetShoreVertices :=
    (mem_targetShoreDarts d x).mp hxIn
  have hxTarget : x.target ∉ d.targetShoreVertices := by
    simpa only [mem_targetShoreDarts, contourSucc_source] using hxOut
  have hedge := edgeSym2_eq_of_source_mem_target_notMem d x hxSource hxTarget
  rw [edgeSym2, edgeSym2, Sym2.eq_iff] at hedge
  rcases hedge with ⟨hss, htt⟩ | ⟨hst, hts⟩
  · have hdSourceOut := source_notMem_targetShoreVertices hacyc d
    exact (hdSourceOut (hss ▸ hxSource)).elim
  · apply ext_endpoints
    · simpa [reverse] using hst
    · simpa [reverse] using hts

/-- The original dart is the unique contour state entering its target shore. -/
theorem eq_of_notMem_targetShore_of_contourSucc_mem
    (hacyc : T.IsAcyclic) (d x : GridDirectionalDart T)
    (hxOut : x ∉ d.targetShoreDarts)
    (hxIn : x.contourSucc ∈ d.targetShoreDarts) :
    x = d := by
  have hxSource : x.source ∉ d.targetShoreVertices := by
    simpa only [mem_targetShoreDarts] using hxOut
  have hxTarget : x.target ∈ d.targetShoreVertices := by
    simpa only [mem_targetShoreDarts, contourSucc_source] using hxIn
  have hedge := edgeSym2_eq_of_source_mem_target_notMem d x.reverse
    (by simpa [reverse] using hxTarget)
    (by simpa [reverse] using hxSource)
  rw [edgeSym2, edgeSym2, reverse, Sym2.eq_iff] at hedge
  rcases hedge with ⟨hts, hst⟩ | ⟨htt, hss⟩
  · have hdSourceOut := source_notMem_targetShoreVertices hacyc d
    exact (hdSourceOut (hts ▸ hxTarget)).elim
  · apply ext_endpoints
    · exact hss
    · exact htt

/-- Exact unique-entry characterization of a fundamental contour shore. -/
theorem contourSucc_mem_targetShore_iff_of_notMem
    (hacyc : T.IsAcyclic) (d x : GridDirectionalDart T)
    (hxOut : x ∉ d.targetShoreDarts) :
    x.contourSucc ∈ d.targetShoreDarts ↔ x = d := by
  constructor
  · exact eq_of_notMem_targetShore_of_contourSucc_mem hacyc d x hxOut
  · intro h
    subst x
    rw [mem_targetShoreDarts]
    simpa only [contourSucc_source] using target_mem_targetShoreVertices d

/-- Exact unique-exit characterization of a fundamental contour shore. -/
theorem contourSucc_notMem_targetShore_iff_of_mem
    (hacyc : T.IsAcyclic) (d x : GridDirectionalDart T)
    (hxIn : x ∈ d.targetShoreDarts) :
    x.contourSucc ∉ d.targetShoreDarts ↔ x = d.reverse := by
  constructor
  · exact eq_reverse_of_mem_targetShore_of_contourSucc_notMem hacyc d x hxIn
  · intro h
    subst x
    rw [mem_targetShoreDarts]
    have hsource := source_notMem_targetShoreVertices hacyc d
    simpa only [contourSucc_source, reverse] using hsource

/-- The two orientations of every tree edge lie in the same contour orbit. -/
theorem contourEquiv_sameCycle_reverse
    (hacyc : T.IsAcyclic) (d : GridDirectionalDart T) :
    Equiv.Perm.SameCycle (contourEquiv (T := T)) d d.reverse := by
  apply Equiv.Perm.sameCycle_of_unique_leave
    (contourEquiv (T := T)) d.targetShoreDarts
  · rw [mem_targetShoreDarts]
    exact source_notMem_targetShoreVertices hacyc d
  · rw [mem_targetShoreDarts]
    change d.contourSucc.source ∈ d.targetShoreVertices
    simpa only [contourSucc_source] using target_mem_targetShoreVertices d
  · intro x hxIn hxOut
    apply eq_reverse_of_mem_targetShore_of_contourSucc_notMem hacyc d x hxIn
    change x.contourSucc ∉ d.targetShoreDarts at hxOut
    exact hxOut

private theorem contourEquiv_sameCycle_contourSucc
    (d : GridDirectionalDart T) :
    Equiv.Perm.SameCycle (contourEquiv (T := T)) d d.contourSucc := by
  refine ⟨1, ?_⟩
  change (contourEquiv (T := T)) d = d.contourSucc
  rfl

/-- Outgoing darts consecutive in the local clockwise rotation lie in the same
global contour orbit. -/
private theorem contourEquiv_sameCycle_localNext
    (hacyc : T.IsAcyclic) (a b : GridDirectionalDart T)
    (hsource : b.source = a.source)
    (hdirection : b.direction =
      a.direction.nextIn (directionsAt (T := T) a.source)) :
    Equiv.Perm.SameCycle (contourEquiv (T := T)) a b := by
  have hreverse := contourEquiv_sameCycle_reverse hacyc a
  have hstep := contourEquiv_sameCycle_contourSucc a.reverse
  have hnext : a.reverse.contourSucc = b := by
    apply ext
    · simpa [reverse] using hsource.symm
    · simpa [reverse] using hdirection.symm
  rw [hnext] at hstep
  exact hreverse.trans hstep

/-- All outgoing darts at one vertex lie in the same contour orbit. -/
theorem contourEquiv_sameCycle_of_source_eq
    (hacyc : T.IsAcyclic) {a b : GridDirectionalDart T}
    (hsource : a.source = b.source) :
    Equiv.Perm.SameCycle (contourEquiv (T := T)) a b := by
  let S := directionsAt (T := T) a.source
  have ha : a.direction ∈ S := by
    rw [mem_directionsAt]
    exact ⟨a.target, a.step, a.adj⟩
  have hb : b.direction ∈ S := by
    rw [mem_directionsAt]
    have hstep : gridNeighbor? a.source b.direction = some b.target := by
      simpa only [hsource] using b.step
    have hadj : T.Adj a.source b.target := by
      simpa only [hsource] using b.adj
    exact ⟨b.target, hstep, hadj⟩
  have hor :=
    GridDirection.mem_eq_or_eq_nextIn_or_eq_nextIn_two_or_eq_nextIn_three
      S ha hb
  rcases hor with hzero | hone | htwo | hthree
  · exact (ext hsource hzero.symm).sameCycle (contourEquiv (T := T))
  · exact contourEquiv_sameCycle_localNext hacyc a b hsource.symm hone
  · let c := ofDirectionMem (T := T) a.source (a.direction.nextIn S)
      (GridDirection.nextIn_mem ha)
    have hac : Equiv.Perm.SameCycle (contourEquiv (T := T)) a c :=
      contourEquiv_sameCycle_localNext hacyc a c rfl rfl
    have hcb : Equiv.Perm.SameCycle (contourEquiv (T := T)) c b := by
      apply contourEquiv_sameCycle_localNext hacyc c b
      · exact hsource.symm
      · simpa [c, S] using htwo
    exact hac.trans hcb
  · let c := ofDirectionMem (T := T) a.source (a.direction.nextIn S)
      (GridDirection.nextIn_mem ha)
    let e := ofDirectionMem (T := T) a.source
      ((a.direction.nextIn S).nextIn S)
      (GridDirection.nextIn_mem (GridDirection.nextIn_mem ha))
    have hac : Equiv.Perm.SameCycle (contourEquiv (T := T)) a c :=
      contourEquiv_sameCycle_localNext hacyc a c rfl rfl
    have hce : Equiv.Perm.SameCycle (contourEquiv (T := T)) c e := by
      apply contourEquiv_sameCycle_localNext hacyc c e <;> rfl
    have heb : Equiv.Perm.SameCycle (contourEquiv (T := T)) e b := by
      apply contourEquiv_sameCycle_localNext hacyc e b
      · exact hsource.symm
      · simpa [e, S] using hthree
    exact hac.trans (hce.trans heb)

/-- Darts based at adjacent tree vertices lie in the same contour orbit. -/
theorem contourEquiv_sameCycle_of_adj_sources
    (hTgrid : T ≤ gridGraph m n) (hacyc : T.IsAcyclic)
    {a b : GridDirectionalDart T} (hab : T.Adj a.source b.source) :
    Equiv.Perm.SameCycle (contourEquiv (T := T)) a b := by
  obtain ⟨d, hdSource, hdTarget⟩ := exists_of_adj hTgrid hab
  have had := contourEquiv_sameCycle_of_source_eq hacyc
    (a := a) (b := d) hdSource.symm
  have hreverse := contourEquiv_sameCycle_reverse hacyc d
  have hrb := contourEquiv_sameCycle_of_source_eq hacyc
    (a := d.reverse) (b := b) (by simp [reverse, hdTarget])
  exact had.trans (hreverse.trans hrb)

/-- The contour permutation of an embedded grid tree consists of one orbit. -/
theorem contourEquiv_sameCycle
    (hTgrid : T ≤ gridGraph m n) (htree : T.IsTree)
    (a b : GridDirectionalDart T) :
    Equiv.Perm.SameCycle (contourEquiv (T := T)) a b := by
  obtain ⟨p⟩ := htree.connected.preconnected a.source b.source
  have walk_same : ∀ {u v : GridVertex m n} (q : T.Walk u v)
      (x y : GridDirectionalDart T), x.source = u → y.source = v →
        Equiv.Perm.SameCycle (contourEquiv (T := T)) x y := by
    intro u v q
    induction q with
    | nil =>
        intro x y hx hy
        apply contourEquiv_sameCycle_of_source_eq htree.isAcyclic
        exact hx.trans hy.symm
    | cons hadj q ih =>
        intro x y hx hy
        obtain ⟨d, hdSource, hdTarget⟩ := exists_of_adj hTgrid hadj
        have hxd := contourEquiv_sameCycle_of_source_eq htree.isAcyclic
          (a := x) (b := d) (hx.trans hdSource.symm)
        have hreverse := contourEquiv_sameCycle_reverse htree.isAcyclic d
        have hrest := ih d.reverse y (by simp [reverse, hdTarget]) hy
        exact hxd.trans (hreverse.trans hrest)
  exact walk_same p a b rfl rfl

/-- In nontrivial grids the contour successor is a single nontrivial cycle. -/
theorem contourEquiv_isCycle
    (hTgrid : T ≤ gridGraph m n) (htree : T.IsTree)
    (d : GridDirectionalDart T) :
    Equiv.Perm.IsCycle (contourEquiv (T := T)) := by
  refine ⟨d, contourSucc_ne d, ?_⟩
  intro y _
  exact contourEquiv_sameCycle hTgrid htree d y

end GridDirectionalDart

end GridGraphs
