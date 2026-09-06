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
      (Finset.card_filter_add_card_filter_not
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

/-! ## Roots grouped by a physical port -/

/-- Physical ports used by at least one root.  This is the finite quotient of
the occurrence-labelled roots by equality of their physical port. -/
def usedRootPorts {P : Type*} [DecidableEq P]
    (rootPort : ↥F.roots → P) : Finset P :=
  Finset.univ.image rootPort

/-- Number of occurrence-labelled roots above one physical port. -/
def rootPortMultiplicity {P : Type*} [DecidableEq P]
    (rootPort : ↥F.roots → P) (port : P) : Nat :=
  (Finset.univ.filter fun root => rootPort root = port).card

/-- Repeated roots above a used physical port, after retaining one quotient
root.  These units must be paid by branch, component, or internal resources;
they are not fresh physical ports. -/
def rootPortDebt {P : Type*} [DecidableEq P]
    (rootPort : ↥F.roots → P) : Nat :=
  ∑ port ∈ F.usedRootPorts rootPort, (F.rootPortMultiplicity rootPort port - 1)

/-- Concrete copies of all duplicate-root debt units. -/
def RootPortDebtSlot {P : Type*} [DecidableEq P]
    (rootPort : ↥F.roots → P) :=
  Σ port : ↥(F.usedRootPorts rootPort),
    Fin (F.rootPortMultiplicity rootPort port.1 - 1)

noncomputable instance rootPortDebtSlotFintype {P : Type*} [DecidableEq P]
    (rootPort : ↥F.roots → P) : Fintype (F.RootPortDebtSlot rootPort) := by
  unfold RootPortDebtSlot
  infer_instance

omit [DecidableEq V] in
theorem card_rootPortDebtSlot {P : Type*} [DecidableEq P]
    (rootPort : ↥F.roots → P) :
    Fintype.card (F.RootPortDebtSlot rootPort) = F.rootPortDebt rootPort := by
  unfold RootPortDebtSlot
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, rootPortDebt]
  exact Finset.sum_attach (F.usedRootPorts rootPort)
    (fun port => F.rootPortMultiplicity rootPort port - 1)

omit [DecidableEq V] in
/-- Exact finite multiplicity formula: occurrence roots are one representative
per used physical port plus all duplicate-root debt. -/
theorem card_usedRootPorts_add_rootPortDebt {P : Type*} [DecidableEq P]
    (rootPort : ↥F.roots → P) :
    (F.usedRootPorts rootPort).card + F.rootPortDebt rootPort = F.roots.card := by
  have hsum : F.roots.card =
      ∑ port ∈ F.usedRootPorts rootPort, F.rootPortMultiplicity rootPort port := by
    simpa only [usedRootPorts, rootPortMultiplicity, Finset.card_univ,
      Fintype.card_coe] using
      Finset.card_eq_sum_card_image rootPort (Finset.univ : Finset ↥F.roots)
  have hpositive : ∀ port ∈ F.usedRootPorts rootPort,
      1 ≤ F.rootPortMultiplicity rootPort port := by
    intro port hport
    obtain ⟨root, -, hroot⟩ := Finset.mem_image.mp hport
    apply Nat.one_le_iff_ne_zero.mpr
    intro hzero
    rw [rootPortMultiplicity, Finset.card_eq_zero] at hzero
    have : root ∈ (Finset.univ.filter fun r => rootPort r = port) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroot⟩
    rw [hzero] at this
    simp at this
  calc
    (F.usedRootPorts rootPort).card + F.rootPortDebt rootPort =
        ∑ port ∈ F.usedRootPorts rootPort,
          (1 + (F.rootPortMultiplicity rootPort port - 1)) := by
      rw [rootPortDebt, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    _ = ∑ port ∈ F.usedRootPorts rootPort,
          F.rootPortMultiplicity rootPort port := by
      apply Finset.sum_congr rfl
      intro port hport
      exact Nat.add_sub_of_le (hpositive port hport)
    _ = F.roots.card := hsum.symm

omit [DecidableEq V] in
/-- Pointwise root-port injectivity is exactly the exceptional zero-debt case. -/
theorem rootPortDebt_eq_zero_iff_injective {P : Type*} [DecidableEq P]
    (rootPort : ↥F.roots → P) :
    F.rootPortDebt rootPort = 0 ↔ Function.Injective rootPort := by
  constructor
  · intro hzero a b hab
    apply (Finset.card_image_iff.mp ?_) (Finset.mem_univ a)
      (Finset.mem_univ b) hab
    have hcount := F.card_usedRootPorts_add_rootPortDebt rootPort
    simpa [usedRootPorts, hzero] using hcount
  · intro hinjective
    have himage : (F.usedRootPorts rootPort).card = F.roots.card := by
      rw [usedRootPorts, Finset.card_image_of_injective _ hinjective,
        Finset.card_univ, Fintype.card_coe]
    have hcount := F.card_usedRootPorts_add_rootPortDebt rootPort
    omega

/-- Euler accounting after quotienting roots by their physical port. -/
theorem card_leaves_eq_usedRootPorts_add_debt_add_branchExcess
    {P : Type*} [DecidableEq P] (rootPort : ↥F.roots → P) :
    F.leaves.card = (F.usedRootPorts rootPort).card +
      F.rootPortDebt rootPort + F.branchExcess := by
  rw [F.card_leaves_eq_card_roots_add_branchExcess,
    ← F.card_usedRootPorts_add_rootPortDebt rootPort]

/-- A grouped root ledger asks for one resource per used physical port and one
resource per duplicate or merger unit.  It never assumes a fresh physical port
for every occurrence root. -/
structure GroupedRootLedger {P R : Type*} [DecidableEq P]
    (rootPort : ↥F.roots → P) where
  resource : (↥(F.usedRootPorts rootPort) ⊕
    (F.RootPortDebtSlot rootPort ⊕ F.MergerSlot)) ↪ R

theorem GroupedRootLedger.card_leaves_le_resource
    {P R : Type*} [DecidableEq P] [Fintype R]
    (rootPort : ↥F.roots → P)
    (ledger : F.GroupedRootLedger (R := R) rootPort) :
    F.leaves.card ≤ Fintype.card R := by
  have h := Fintype.card_le_of_injective ledger.resource ledger.resource.injective
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_coe,
    F.card_rootPortDebtSlot, F.card_mergerSlot] at h
  rw [F.card_leaves_eq_usedRootPorts_add_debt_add_branchExcess rootPort]
  omega

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
