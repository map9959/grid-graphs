import GridGraphs.ForcedExchange
import GridGraphs.GridDirection
import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex

/-!
# Canonical insertion circuits

This file records only the finite choices used by the insertion-circuit
computation.  For an omitted vertex of a one-vertex-maximal forced forest, an
attachment pair consists of two distinct members of
`{u} ∪ (G.neighborSet u \ F)` that are connected in the old forced graph.  The
pair is ordered to avoid counting its reversal a second time.

The associated path is independent of choice because the old forced graph is
acyclic.  On a grid, candidates are ordered by the computational key
`(number of circuit edges, sorted normalized undirected edge list)`; the pair
itself is only a deterministic tertiary tie-breaker.  No weighted estimate is
asserted here.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {V : Type*}

/-- Row-major lexicographic order on grid vertices.  Products normally carry
the componentwise partial order, so insertion-circuit tie-breaking installs
the explicit lexicographic order required by the computation. -/
noncomputable instance gridVertexLinearOrder (m n : Nat) :
    LinearOrder (GridVertex m n) :=
  LinearOrder.lift'
    (fun v => (toLex (v.1, v.2) : Fin m ×ₗ Fin n))
    (fun a b h => by
      have hab : (a.1, a.2) = (b.1, b.2) := toLex_inj.mp h
      exact Prod.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab))

/-- An omitted owner, with maximality retained as provenance rather than
reconstructed from the existence of one attachment pair. -/
structure MaximalOmittedVertex (G : SimpleGraph V) (F : Set V) where
  owner : V
  omitted : owner ∉ F
  maximal : MaximalForcedAcyclic G F

/-- The attachment universe for insertion at `u`.  Taking `v = u` represents
the one-new-edge circuit; a neighbor outside `F` represents a new edge owned
by this insertion. -/
def IsInsertionAttachment (G : SimpleGraph V) (F : Set V) (u v : V) : Prop :=
  v = u ∨ (G.Adj u v ∧ v ∉ F)

/-- A normalized pair of distinct attachment vertices already joined in the
old forced forest.  Its two fields retain the multiplicity of two distinct
star leaves, while the surrounding omitted vertex retains edge ownership. -/
structure InsertionAttachmentPair [LinearOrder V]
    (G : SimpleGraph V) (F : Set V) (u : V) where
  left : V
  right : V
  left_mem : IsInsertionAttachment G F u left
  right_mem : IsInsertionAttachment G F u right
  ordered : left < right
  reachable : (forcedEdgeGraph G F).Reachable left right

namespace InsertionAttachmentPair

variable [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (F : Set V)

omit [Fintype V] [DecidableRel G.Adj] in
@[ext] theorem ext {u : V} {p q : InsertionAttachmentPair G F u}
    (hleft : p.left = q.left) (hright : p.right = q.right) : p = q := by
  cases p
  cases q
  simp_all

instance {u : V} : Finite (InsertionAttachmentPair G F u) :=
  Finite.of_injective
    (fun p : InsertionAttachmentPair G F u => (p.left, p.right))
    (fun _ _ h => ext G F (congrArg Prod.fst h) (congrArg Prod.snd h))

noncomputable instance {u : V} : Fintype (InsertionAttachmentPair G F u) :=
  Fintype.ofFinite _

instance {u : V} : DecidableEq (InsertionAttachmentPair G F u) :=
  fun p q =>
    if hleft : p.left = q.left then
      if hright : p.right = q.right then isTrue (ext G F hleft hright)
      else isFalse (fun h => hright (congrArg InsertionAttachmentPair.right h))
    else isFalse (fun h => hleft (congrArg InsertionAttachmentPair.left h))

/-- Maximality supplies at least one normalized attachment pair for every
omitted owner. -/
theorem nonempty (x : MaximalOmittedVertex G F) :
    Nonempty (InsertionAttachmentPair G F x.owner) := by
  classical
  obtain ⟨v, hv, w, hw, hvw, hreach⟩ :=
    (maximalForcedAcyclic_iff_reachable.mp x.maximal).2 x.owner x.omitted
  have hv' : IsInsertionAttachment G F x.owner v := by
    simpa [IsInsertionAttachment] using hv
  have hw' : IsInsertionAttachment G F x.owner w := by
    simpa [IsInsertionAttachment] using hw
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · exact ⟨⟨v, w, hv', hw', hvwlt, hreach⟩⟩
  · exact ⟨⟨w, v, hw', hv', hwvlt, hreach.symm⟩⟩

/-- A path chosen from reachability.  Its uniqueness below, rather than the
implementation of `Classical.choice`, is what makes this path canonical. -/
noncomputable def path {u : V} (p : InsertionAttachmentPair G F u) :
    (forcedEdgeGraph G F).Walk p.left p.right :=
  (Classical.choice p.reachable).toPath

omit [Fintype V] [DecidableRel G.Adj] in
theorem path_isPath {u : V} (p : InsertionAttachmentPair G F u) :
    (p.path G F).IsPath :=
  (Classical.choice p.reachable).toPath.property

omit [Fintype V] [DecidableRel G.Adj] in
/-- Any simple old-forest path between the selected attachments is the path
stored above. -/
theorem path_unique (hacyclic : (forcedEdgeGraph G F).IsAcyclic)
    {u : V} (p : InsertionAttachmentPair G F u)
    (q : (forcedEdgeGraph G F).Walk p.left p.right) (hq : q.IsPath) :
    q = p.path G F := by
  have h := (hacyclic.subsingleton_path _ _).elim
    (⟨q, hq⟩ : (forcedEdgeGraph G F).Path p.left p.right)
    (⟨p.path G F, p.path_isPath G F⟩ :
      (forcedEdgeGraph G F).Path p.left p.right)
  exact congrArg Subtype.val h

/-- A path together with the property that it is the only simple path between
its endpoints. -/
structure UniqueForestPath (H : SimpleGraph V) (v w : V) where
  path : H.Walk v w
  isPath : path.IsPath
  unique : ∀ q : H.Walk v w, q.IsPath → q = path

/-- Package the attachment path with its forest uniqueness certificate. -/
noncomputable def uniqueForestPath (hacyclic : (forcedEdgeGraph G F).IsAcyclic)
    {u : V} (p : InsertionAttachmentPair G F u) :
    UniqueForestPath (forcedEdgeGraph G F) p.left p.right where
  path := p.path G F
  isPath := p.path_isPath G F
  unique := p.path_unique G F hacyclic

end InsertionAttachmentPair

/-- Row-major normalization of an undirected edge. -/
def normalizedVertexPair [LinearOrder V] (v w : V) : Lex (V × V) :=
  toLex (if v ≤ w then (v, w) else (w, v))

/-- The normalized undirected edges traversed by a walk, in traversal order. -/
def walkNormalizedEdges [LinearOrder V] {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) : List (Lex (V × V)) :=
  List.zipWith normalizedVertexPair p.support p.support.tail

/-- The new owner-labelled edges represented by an attachment pair.  An
endpoint equal to the owner contributes no edge; all other endpoints retain
one occurrence. -/
def insertionEdges [LinearOrder V] (u : V) (v w : V) :
    List (Lex (V × V)) :=
  (if v = u then [] else [normalizedVertexPair u v]) ++
    (if w = u then [] else [normalizedVertexPair u w])

/-- Exact key used by the finite computation: circuit edge count, followed by
the sorted normalized undirected edge list. -/
noncomputable def insertionCircuitKey {m n : Nat} (F : Set (GridVertex m n))
    (u : GridVertex m n)
    (p : InsertionAttachmentPair (gridGraph m n) F u) :
    Lex (Nat × List (Lex (GridVertex m n × GridVertex m n))) := by
  classical
  let edges := insertionEdges u p.left p.right ++
    walkNormalizedEdges (p.path (gridGraph m n) F)
  exact toLex (edges.length, edges.mergeSort)

/-- Canonical attachment pair for the exact computational ordering.  The
normalized pair is a tertiary key only, making the minimizer deterministic if
two candidates have the same circuit key. -/
noncomputable def canonicalInsertionAttachmentPair {m n : Nat}
    (F : Set (GridVertex m n))
    (x : MaximalOmittedVertex (gridGraph m n) F) :
    InsertionAttachmentPair (gridGraph m n) F x.owner := by
  classical
  letI : Nonempty (InsertionAttachmentPair (gridGraph m n) F x.owner) :=
    InsertionAttachmentPair.nonempty (gridGraph m n) F x
  let candidates :=
    (Finset.univ : Finset (InsertionAttachmentPair (gridGraph m n) F x.owner))
  let orderedKey := fun p =>
    toLex (insertionCircuitKey F x.owner p,
      toLex (p.left, p.right))
  exact Classical.choose
    (Finset.exists_min_image candidates orderedKey
      Finset.univ_nonempty)

/-- The selected pair minimizes the exact two-part computational key. -/
theorem canonicalInsertionAttachmentPair_minimal {m n : Nat}
    (F : Set (GridVertex m n))
    (x : MaximalOmittedVertex (gridGraph m n) F)
    (p : InsertionAttachmentPair (gridGraph m n) F x.owner) :
    insertionCircuitKey F x.owner
        (canonicalInsertionAttachmentPair F x) ≤
      insertionCircuitKey F x.owner p := by
  classical
  let : Nonempty (InsertionAttachmentPair (gridGraph m n) F x.owner) :=
    InsertionAttachmentPair.nonempty (gridGraph m n) F x
  let candidates :=
    (Finset.univ : Finset (InsertionAttachmentPair (gridGraph m n) F x.owner))
  let orderedKey := fun p =>
    toLex (insertionCircuitKey F x.owner p,
      toLex (p.left, p.right))
  have hle := (Classical.choose_spec
    (Finset.exists_min_image candidates orderedKey Finset.univ_nonempty)).2
      p (Finset.mem_univ p)
  exact @Prod.Lex.monotone_fst _ _ inferInstance
    (inferInstance : LinearOrder (Lex (GridVertex m n × GridVertex m n))).toLE _ _ hle

/-- Horizontal or vertical orientation, forgetting the direction of travel. -/
inductive GridAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Axis of a grid segment.  Circuit callers supply adjacent vertices; for
such vertices equality of rows is exactly horizontality. -/
def gridSegmentAxis {m n : Nat} (v w : GridVertex m n) : GridAxis :=
  if v.1 = w.1 then .horizontal else .vertical

/-- Axes traversed by a walk, in traversal order. -/
def walkAxes {m n : Nat} {G : SimpleGraph (GridVertex m n)} {v w}
    (p : G.Walk v w) : List GridAxis :=
  List.zipWith gridSegmentAxis p.support p.support.tail

/-- Count changes in a cyclic nonempty list. -/
private def cyclicChangesFrom [DecidableEq α] (first previous : α) :
    List α → Nat
  | [] => if previous = first then 0 else 1
  | next :: rest =>
      (if previous = next then 0 else 1) +
        cyclicChangesFrom first next rest

/-- Number of cyclic changes between consecutive entries. -/
def cyclicChangeCount [DecidableEq α] : List α → Nat
  | [] => 0
  | first :: rest => cyclicChangesFrom first first rest

/-- Orthogonal turn count of an insertion candidate.  The list consists of
the one or two new owner edges and the uniquely determined old-forest path;
cyclic comparison includes both joins. -/
noncomputable def insertionOrthogonalTurnCount {m n : Nat}
    (F : Set (GridVertex m n)) (u : GridVertex m n)
    (p : InsertionAttachmentPair (gridGraph m n) F u) : Nat :=
  let first := if p.left = u then [] else [gridSegmentAxis u p.left]
  let last := if p.right = u then [] else [gridSegmentAxis p.right u]
  cyclicChangeCount (first ++ walkAxes (p.path (gridGraph m n) F) ++ last)

/-- Minimal data exported for the canonical insertion circuit.  The path is
accessed through `pair.path`; its uniqueness follows from `owner.maximal.1`. -/
structure CanonicalInsertionCircuit {m n : Nat}
    (F : Set (GridVertex m n)) where
  owner : MaximalOmittedVertex (gridGraph m n) F
  pair : InsertionAttachmentPair (gridGraph m n) F owner.owner
  pair_eq : pair = canonicalInsertionAttachmentPair F owner
  turns : Nat
  turns_eq : turns = insertionOrthogonalTurnCount F owner.owner pair

/-- Package the canonical choices without adding any numerical estimate. -/
noncomputable def canonicalInsertionCircuit {m n : Nat}
    (F : Set (GridVertex m n))
    (x : MaximalOmittedVertex (gridGraph m n) F) :
    CanonicalInsertionCircuit F where
  owner := x
  pair := canonicalInsertionAttachmentPair F x
  pair_eq := rfl
  turns := insertionOrthogonalTurnCount F x.owner
    (canonicalInsertionAttachmentPair F x)
  turns_eq := rfl

end GridGraphs
