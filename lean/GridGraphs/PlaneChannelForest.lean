import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Abstract channel-forest pruning

This file isolates the finite combinatorial count used after a planar channel
construction has been obtained.  A `ParentForest` is a finite parent map whose
rank strictly decreases towards a root.  Thus parent chains terminate and
directed cycles are excluded.

The main identity says that the number of leaves is the number of roots plus
the total branching excess.  A `PlaneChannelForest` additionally marks demand
vertices and exits.  If every demand either survives as a leaf or is stopped at
an exit, the identity gives an injection into exits, merger slots, and roots.

Nothing here constructs channels from a grid embedding, proves planarity or
noncrossing, or shows that grid demands satisfy the pruning hypothesis.  Those
geometric obligations deliberately remain outside this abstract theorem.
-/

namespace GridGraphs

open Finset

/-- A finite directed forest, presented by its parent map.  The rank condition
is the structural acyclicity condition and orients every edge towards a root. -/
structure ParentForest (V : Type*) where
  parent : V → Option V
  rank : V → Nat
  rank_parent : ∀ {v w}, parent v = some w → rank w < rank v

namespace ParentForest

variable {V : Type*} [Fintype V] [DecidableEq V] (F : ParentForest V)

/-- Vertices with no parent, i.e. root/carrier terminals. -/
def roots : Finset V := Finset.univ.filter fun v => F.parent v = none

/-- Children of a vertex in the parent orientation. -/
def children (v : V) : Finset V :=
  Finset.univ.filter fun w => F.parent w = some v

/-- Number of incoming child branches at a vertex. -/
def childCount (v : V) : Nat := (F.children v).card

/-- Vertices at which no further child branch remains. -/
def leaves : Finset V := Finset.univ.filter fun v => F.childCount v = 0

/-- A vertex with two or more children is a merger.  Its number of additional
branches, beyond the first continuing branch, is its merger excess. -/
def mergerExcessAt (v : V) : Nat := F.childCount v - 1

/-- The distinguished merger vertices, characterized by at least two child
branches. -/
def mergers : Finset V := Finset.univ.filter fun v => 2 ≤ F.childCount v

@[simp] theorem mem_mergers (v : V) : v ∈ F.mergers ↔ 2 ≤ F.childCount v := by
  simp [mergers]

/-- Exactly the merger vertices carry positive merger excess. -/
theorem mergerExcessAt_pos_iff (v : V) :
    0 < F.mergerExcessAt v ↔ v ∈ F.mergers := by
  simp [mergerExcessAt, Nat.sub_pos_iff_lt, Nat.succ_le_iff]

/-- Total merger excess in the forest.  Unary and leaf vertices contribute
zero, so this sum is supported exactly on merger vertices. -/
def branchExcess : Nat := ∑ v, F.mergerExcessAt v

/-- Concrete copies of all merger excess units. -/
def MergerSlot := Σ v : V, Fin (F.mergerExcessAt v)

noncomputable instance mergerSlotFintype : Fintype F.MergerSlot := by
  unfold MergerSlot
  infer_instance

theorem card_mergerSlot : Fintype.card F.MergerSlot = F.branchExcess := by
  change Fintype.card (Σ v : V, Fin (F.mergerExcessAt v)) = F.branchExcess
  rw [Fintype.card_sigma]
  simp [branchExcess]

/-- Counting parent fibers: every vertex is either a root or contributes once
as a child of its unique parent. -/
private theorem sum_childCount_add_card_roots :
    (∑ v, F.childCount v) + F.roots.card = Fintype.card V := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := F.parent)
    (s := (Finset.univ : Finset V))
    (t := (Finset.univ : Finset (Option V)))
    (by intro v _; exact Finset.mem_univ (F.parent v))
  simpa [univ_option, Finset.insertNone, childCount, children, roots, add_comm] using h.symm

/-- At each nonleaf, one child is the continuing branch and all remaining
children are merger excess. -/
private theorem sum_childCount_eq_branchExcess_add_nonleaves :
    (∑ v, F.childCount v) =
      F.branchExcess + ((Finset.univ.filter fun v => F.childCount v ≠ 0).card) := by
  rw [branchExcess]
  calc
    ∑ v, F.childCount v =
        ∑ v, (F.mergerExcessAt v + if F.childCount v = 0 then 0 else 1) := by
          apply Finset.sum_congr rfl
          intro v _
          unfold mergerExcessAt
          split
          · simp_all
          · rename_i h
            exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)).symm
    _ = (∑ v, F.mergerExcessAt v) +
        ∑ v, (if F.childCount v = 0 then 0 else 1) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ v, F.mergerExcessAt v) +
        (Finset.univ.filter fun v => F.childCount v ≠ 0).card := by
          congr 1
          calc
            ∑ v, (if F.childCount v = 0 then 0 else 1) =
                ∑ v ∈ Finset.univ.filter (fun v => F.childCount v ≠ 0), 1 := by
                  rw [Finset.sum_filter]
                  apply Finset.sum_congr rfl
                  intro v _
                  split <;> simp_all
            _ = (Finset.univ.filter fun v => F.childCount v ≠ 0).card := by simp

/-- Exact leaf ledger for a finite parent forest.

The result is componentwise in aggregate: each root supplies one initial
branch, and each merger excess supplies one additional terminal leaf. -/
theorem card_leaves_eq_card_roots_add_branchExcess :
    F.leaves.card = F.roots.card + F.branchExcess := by
  have hedge := F.sum_childCount_add_card_roots
  have hbranch := F.sum_childCount_eq_branchExcess_add_nonleaves
  have hpartition :
      F.leaves.card + (Finset.univ.filter fun v => F.childCount v ≠ 0).card =
        Fintype.card V := by
    rw [leaves]
    simpa [Finset.filter_not] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset V)) (p := fun v => F.childCount v = 0))
  have hcancel :
      F.leaves.card + (Finset.univ.filter fun v => F.childCount v ≠ 0).card =
        (F.roots.card + F.branchExcess) +
          (Finset.univ.filter fun v => F.childCount v ≠ 0).card := by
    calc
      F.leaves.card + (Finset.univ.filter fun v => F.childCount v ≠ 0).card =
          Fintype.card V := hpartition
      _ = (∑ v, F.childCount v) + F.roots.card := hedge.symm
      _ = (F.branchExcess +
            (Finset.univ.filter fun v => F.childCount v ≠ 0).card) +
            F.roots.card := by rw [hbranch]
      _ = (F.roots.card + F.branchExcess) +
            (Finset.univ.filter fun v => F.childCount v ≠ 0).card := by
        ac_rfl
  exact Nat.add_right_cancel hcancel

end ParentForest

/-- Abstract data left after a planar channel pruning argument.  `demand` and
`exits` are distinguished vertex sets; the forest itself supplies merger and
root resources. -/
structure PlaneChannelForest (V : Type*) [Fintype V] [DecidableEq V] where
  forest : ParentForest V
  demand : Finset V
  exits : Finset V
  demand_leaf_or_exit : demand ⊆ forest.leaves ∪ exits

namespace PlaneChannelForest

variable {V : Type*} [Fintype V] [DecidableEq V] (C : PlaneChannelForest V)

/-- The resource type appearing in the pruning bound: an exit, one unit of
merger excess, or a root/carrier terminal. -/
def Resource :=
  (↥C.exits) ⊕ (C.forest.MergerSlot ⊕ (↥C.forest.roots))

noncomputable instance resourceFintype : Fintype C.Resource := by
  unfold Resource
  infer_instance

theorem card_resource :
    Fintype.card C.Resource =
      C.exits.card + C.forest.branchExcess + C.forest.roots.card := by
  simp [Resource, ParentForest.card_mergerSlot, Nat.add_assoc]

/-- Abstract Euler/pruning inequality.  Its only channel-specific premise is
the structural coverage assertion in `demand_leaf_or_exit`, not a cardinal
inequality. -/
theorem card_demand_le_exits_add_branchExcess_add_roots :
    C.demand.card ≤
      C.exits.card + C.forest.branchExcess + C.forest.roots.card := by
  calc
    C.demand.card ≤ (C.forest.leaves ∪ C.exits).card :=
      Finset.card_le_card C.demand_leaf_or_exit
    _ ≤ C.forest.leaves.card + C.exits.card :=
      Finset.card_union_le C.forest.leaves C.exits
    _ = C.exits.card + C.forest.branchExcess + C.forest.roots.card := by
      rw [C.forest.card_leaves_eq_card_roots_add_branchExcess]
      ac_rfl

/-- Resource-injection form of the pruning inequality.  The embedding is not
claimed to be a canonical geometric routing; it follows from the finite
cardinality theorem above. -/
noncomputable def demandEmbedding : (↥C.demand) ↪ C.Resource := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_coe, C.card_resource]
  exact C.card_demand_le_exits_add_branchExcess_add_roots

end PlaneChannelForest

end GridGraphs
