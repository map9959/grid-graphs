import GridGraphs.Forests.RootedTreeShore
import GridGraphs.Accounting.PrimalContourLedger
import GridGraphs.Geometry.StraightForcedComponents

/-!
# Noncrossing rooted-shore channels

This file packages the objects needed for a rectilinear proof of the primal
contour inequality.  The `n + 3` sources are `n` row demands and the three
corner sectors different from a chosen root corner.  Their target is the exact
disjoint union counted by boundary deficiency, internal tree edges, and full
components.

No routing existence statement is made here.  Instead, the channel lemmas
record the unconditional mechanism that a routing proof may use: rooted shores
are laminar, one labelled cotree edge occupies a convex set of nested shores,
and that set is exactly the set of rooted tree edges on the cotree edge's tree
path.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

set_option maxHeartbeats 800000

/-- Choice of the horizontal row sweep or its vertical column counterpart. -/
inductive ShoreSweepAxis
  | rows
  | columns
  deriving DecidableEq

/-- The canonical sources for a sweep rooted at one corner: one source for
each row or column and one for each of the other three corner sectors. -/
def CanonicalShoreDemand (_axis : ShoreSweepAxis) (n : Nat) := Fin n ⊕ Fin 3

namespace CanonicalShoreDemand

def row {n : Nat} (r : Fin n) : CanonicalShoreDemand .rows n := Sum.inl r

def column {n : Nat} (c : Fin n) : CanonicalShoreDemand .columns n := Sum.inl c

def northEast {axis : ShoreSweepAxis} {n : Nat} : CanonicalShoreDemand axis n :=
  Sum.inr ⟨0, by omega⟩

def southEast {axis : ShoreSweepAxis} {n : Nat} : CanonicalShoreDemand axis n :=
  Sum.inr ⟨1, by omega⟩

def southWest {axis : ShoreSweepAxis} {n : Nat} : CanonicalShoreDemand axis n :=
  Sum.inr ⟨2, by omega⟩

instance (axis : ShoreSweepAxis) (n : Nat) : Fintype (CanonicalShoreDemand axis n) := by
  unfold CanonicalShoreDemand
  infer_instance

instance (axis : ShoreSweepAxis) (n : Nat) :
    DecidableEq (CanonicalShoreDemand axis n) := by
  unfold CanonicalShoreDemand
  infer_instance

theorem card (axis : ShoreSweepAxis) (n : Nat) :
    Fintype.card (CanonicalShoreDemand axis n) = n + 3 := by
  simp [CanonicalShoreDemand]

end CanonicalShoreDemand

/-- Boundary sectors based at supported vertices.  A corner has two elements
because its grid boundary deficiency is two. -/
def BoundarySector {m n : Nat} (U : Finset (GridVertex m n)) :=
  Σ v : ↥U, Fin (gridBoundaryDeficiency m n v.1)

/-- The three resource types in the base-independent primal contour ledger. -/
def PrimalContourResource {n : Nat}
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj]
    (U : Finset (GridVertex n n)) :=
  BoundarySector U ⊕
    (↥(internalEdgeFinset T U) ⊕
      ((gridGraph n n).induce
        (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
          Set (GridVertex n n))).ConnectedComponent)

noncomputable instance boundarySectorFintype {m n : Nat}
    (U : Finset (GridVertex m n)) : Fintype (BoundarySector U) := by
  unfold BoundarySector
  infer_instance

noncomputable instance primalContourResourceFintype {n : Nat}
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj]
    (U : Finset (GridVertex n n)) : Fintype (PrimalContourResource T U) := by
  unfold PrimalContourResource
  infer_instance

/-- Boundary sectors have exactly the multiplicity encoded by boundary
deficiency, including both sectors at a supported corner. -/
theorem card_boundarySector {m n : Nat} (U : Finset (GridVertex m n)) :
    Fintype.card (BoundarySector U) = boundaryDeficiencySum m n U := by
  classical
  unfold BoundarySector boundaryDeficiencySum
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact U.sum_attach (fun v => gridBoundaryDeficiency m n v)

/-- Exact cardinality of the three-way target ledger. -/
theorem card_primalContourResource {n : Nat}
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj]
    (U : Finset (GridVertex n n)) :
    Fintype.card (PrimalContourResource T U) =
      boundaryDeficiencySum n n U + (internalEdgeFinset T U).card +
        Fintype.card ((gridGraph n n).induce
          (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
            Set (GridVertex n n))).ConnectedComponent := by
  classical
  unfold PrimalContourResource
  rw [Fintype.card_sum, Fintype.card_sum, card_boundarySector]
  simp only [Fintype.card_coe]
  omega

/-- The exact primal ledger expressed as the cardinality of its three concrete
resource types. -/
theorem cotree_incidenceWaste_add_one_eq_card_primalContourResource
    {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    let U := supportFinset (gridGraph n n \ T)
    incidenceWaste (gridGraph n n \ T) + 1 =
      Fintype.card (PrimalContourResource T U) := by
  dsimp only
  rw [card_primalContourResource]
  exact cotree_incidenceWaste_add_one_eq_boundary_add_internal_add_components hn hT

namespace GridDirectionalDart

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- Darts in the channel of a labelled omitted edge, oriented away from a
fixed root. -/
noncomputable def rootedPortChannel (root : GridVertex m n)
    (e : GridEdge m n) : Finset (GridDirectionalDart T) := by
  classical
  exact Finset.univ.filter fun d => AwayFromRoot root d ∧ e ∈ d.cotreePorts

@[simp] theorem mem_rootedPortChannel (root : GridVertex m n)
    (e : GridEdge m n) (d : GridDirectionalDart T) :
    d ∈ rootedPortChannel root e ↔
      AwayFromRoot root d ∧ e ∈ d.cotreePorts := by
  classical
  simp [rootedPortChannel]

/-- Two darts oriented away from one root cannot represent the same tree edge
unless they are equal. -/
theorem eq_of_edgeSym2_eq_of_awayFromRoot (htree : T.IsTree)
    (root : GridVertex m n) {a b : GridDirectionalDart T}
    (ha : AwayFromRoot root a) (hb : AwayFromRoot root b)
    (hedge : a.edgeSym2 = b.edgeSym2) : a = b := by
  rw [edgeSym2, edgeSym2, Sym2.eq_iff] at hedge
  rcases hedge with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ext_endpoints hs ht
  · have har : a = b.reverse := by
      apply ext_endpoints
      · simpa [reverse] using hs
      · simpa [reverse] using ht
    rw [har] at ha
    exact ((awayFromRoot_reverse_iff_not htree root b).1 ha hb).elim

/-- Edge labels are injective on a rooted channel.  Thus opposite orientations
of one attachment cannot be counted as two channel positions. -/
theorem edgeSym2_injective_on_rootedPortChannel (htree : T.IsTree)
    (root : GridVertex m n) (e : GridEdge m n) {a b : GridDirectionalDart T}
    (ha : a ∈ rootedPortChannel root e)
    (hb : b ∈ rootedPortChannel root e)
    (hedge : a.edgeSym2 = b.edgeSym2) : a = b :=
  eq_of_edgeSym2_eq_of_awayFromRoot htree root
    ((mem_rootedPortChannel root e a).1 ha).1
    ((mem_rootedPortChannel root e b).1 hb).1 hedge

/-- Port-path characterization of a rooted channel. -/
theorem mem_rootedPortChannel_iff_mem_path_edges (htree : T.IsTree)
    (root : GridVertex m n) (e : GridEdge m n)
    (he : ¬T.Adj e.primalEndpoints.1 e.primalEndpoints.2)
    (p : T.Walk e.primalEndpoints.1 e.primalEndpoints.2) (hp : p.IsPath)
    (d : GridDirectionalDart T) :
    d ∈ rootedPortChannel root e ↔
      AwayFromRoot root d ∧ d.edgeSym2 ∈ p.edges := by
  rw [mem_rootedPortChannel]
  exact and_congr_right fun _ => mem_cotreePorts_iff_mem_path_edges htree d e he p hp

/-- Shores met by one labelled channel remain convex along every nested chain.
This is the precise no-jumping property needed for noncrossing sweeps. -/
theorem mem_rootedPortChannel_of_nested
    (root : GridVertex m n) (e : GridEdge m n)
    {a b c : GridDirectionalDart T}
    (hab : a.targetShoreVertices ⊆ b.targetShoreVertices)
    (hbc : b.targetShoreVertices ⊆ c.targetShoreVertices)
    (ha : a ∈ rootedPortChannel root e)
    (hb : AwayFromRoot root b)
    (hc : c ∈ rootedPortChannel root e) :
    b ∈ rootedPortChannel root e := by
  rw [mem_rootedPortChannel] at ha hc ⊢
  exact ⟨hb, mem_cotreePorts_of_nested hab hbc ha.2 hc.2⟩

/-- Any two positions occupied by rooted channels have nested or disjoint
shores.  This rules out crossing shore intervals without a lane-routing axiom. -/
theorem rootedPortChannel_shores_laminar (htree : T.IsTree)
    (root : GridVertex m n) {e f : GridEdge m n}
    {a b : GridDirectionalDart T}
    (ha : a ∈ rootedPortChannel root e)
    (hb : b ∈ rootedPortChannel root f) :
    a.targetShoreVertices ⊆ b.targetShoreVertices ∨
      b.targetShoreVertices ⊆ a.targetShoreVertices ∨
      Disjoint a.targetShoreVertices b.targetShoreVertices :=
  targetShoreVertices_laminar htree root
    ((mem_rootedPortChannel root e a).1 ha).1
    ((mem_rootedPortChannel root f b).1 hb).1

end GridDirectionalDart

/-- For a grid-tree cotree support, every full component used by the third
ledger summand is a horizontal or vertical interval carrier. -/
theorem cotree_full_component_straight {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (C : ((gridGraph n n).induce
      (↑((Finset.univ : Finset (GridVertex n n)) \
        supportFinset (gridGraph n n \ T)) :
        Set (GridVertex n n))).ConnectedComponent) :
    (∃ r : Fin n, ∀ v ∈ C.supp, v.1.1 = r) ∨
      ∃ c : Fin n, ∀ v ∈ C.supp, v.1.2 = c := by
  apply induced_forced_connectedComponent_straight
  exact grid_tree_complement_forcedEdgeGraph_isAcyclic hT

/-- An interior leaf of the primal tree is a supported zero-waste cotree
vertex of degree three.  These are precisely the local vertices through which
a putative cotree channel would have to continue without spending a contour
resource. -/
theorem interior_tree_leaf_mem_cotree_support_and_degree_eq_three
    {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) (v : GridVertex m n)
    (hrow : ¬(v.1.val = 0 ∨ v.1.val + 1 = m))
    (hcol : ¬(v.2.val = 0 ∨ v.2.val + 1 = n))
    (hleaf : T.degree v = 1) :
    v ∈ supportFinset (gridGraph m n \ T) ∧
      (gridGraph m n \ T).degree v = 3 ∧
        3 - (gridGraph m n \ T).degree v = 0 := by
  have hgrid : (gridGraph m n).degree v = 4 :=
    gridGraph_degree_interior hm hn v hrow hcol
  have hdegree : (gridGraph m n \ T).degree v = 3 := by
    rw [degree_sdiff_of_le (gridGraph m n) T hT.le, hgrid, hleaf]
  refine ⟨?_, hdegree, by omega⟩
  rw [mem_supportFinset]
  omega

end GridGraphs
