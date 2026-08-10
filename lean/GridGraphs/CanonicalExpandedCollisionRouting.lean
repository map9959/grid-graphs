import GridGraphs.CanonicalExpandedContourForest
import GridGraphs.GridChannelContourRealization
import GridGraphs.JointChannelContourRouting
import GridGraphs.TerminalCarrierQuotientRouting

/-!
# Physical collision routing for the canonical expanded contour

The expanded first-stop forest assigns every merger slot to an unmarked start.
Such a start cannot be a direct exit, so its retained inward tree edge supplies
a physical token.  Existence of the remaining quotient routing is kept as an
explicit hypothesis.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalExpandedContourForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The unique canonical demand represented by a canonical start slot. -/
def demandOfStartSlot (s : ↥(startSlots axis hn2 hT)) :
    CanonicalShoreDemand axis n :=
  (Finset.mem_image.mp s.2).choose

@[simp] theorem startSlot_demandOfStartSlot
    (s : ↥(startSlots axis hn2 hT)) :
    startSlot axis hn2 hT (demandOfStartSlot axis hn2 hT s) = s.1 :=
  (Finset.mem_image.mp s.2).choose_spec.2

theorem demand_eq_demandOfStartSlot
    (hn3 : 3 ≤ n) (s : ↥(startSlots axis hn2 hT))
    (q : CanonicalShoreDemand axis n)
    (hq : startSlot axis hn2 hT q = s.1) :
    q = demandOfStartSlot axis hn2 hT s := by
  apply startSlot_injective axis hn2 hT hn3
  rw [hq, startSlot_demandOfStartSlot axis hn2 hT s]

/-- The canonical expanded construction has exactly the `n + 3` start slots. -/
theorem card_startSlots (hn3 : 3 ≤ n) :
    (startSlots axis hn2 hT).card = n + 3 := by
  rw [startSlots, Finset.card_image_of_injective _
    (startSlot_injective axis hn2 hT hn3), Finset.card_univ,
    CanonicalShoreDemand.card]

/-- An unmarked canonical start recovers an unsupported canonical demand.
Direct starts are outer-port slots and hence are marked. -/
def unsupportedDemandOfUnmarkedStart
    (s : ↥((firstStop axis hn2 hT).starts \ (firstStop axis hn2 hT).stop)) :
    CanonicalShoreDemand.Unsupported axis hn2 T := by
  let s' : ↥(startSlots axis hn2 hT) :=
    ⟨s.1, by simpa [firstStop] using (Finset.mem_sdiff.mp s.2).1⟩
  let q := demandOfStartSlot axis hn2 hT s'
  refine ⟨q, Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, ?_⟩⟩
  intro hdirect
  have hmarked : startSlot axis hn2 hT q ∈ markedSlots (T := T) := by
    rw [startSlot, dif_pos hdirect]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hsnot : s.1 ∉ markedSlots (T := T) := by
    simpa [firstStop] using (Finset.mem_sdiff.mp s.2).2
  apply hsnot
  rw [← startSlot_demandOfStartSlot axis hn2 hT s']
  exact hmarked

/-- Distinct unmarked starts use distinct retained canonical inward edges. -/
noncomputable def unmarkedStartTreeEdgeEmbedding :
    ↥((firstStop axis hn2 hT).starts \ (firstStop axis hn2 hT).stop) ↪
      ↥T.edgeFinset where
  toFun s :=
    let d := GridDirectionalDart.retainedCanonicalInwardDart axis hn2 hT
      (unsupportedDemandOfUnmarkedStart axis hn2 hT s)
    ⟨d.edgeSym2, by
      rw [SimpleGraph.mem_edgeFinset]
      exact d.adj⟩
  inj' := by
    intro s t hst
    let qs := unsupportedDemandOfUnmarkedStart axis hn2 hT s
    let qt := unsupportedDemandOfUnmarkedStart axis hn2 hT t
    have hedge : CanonicalShoreDemand.inwardEdgeSym2 axis hn2 qs.1 =
        CanonicalShoreDemand.inwardEdgeSym2 axis hn2 qt.1 := by
      simpa [qs, qt, GridDirectionalDart.retainedCanonicalInwardDart_edgeSym2]
        using congrArg Subtype.val hst
    have hq : qs.1 = qt.1 :=
      CanonicalShoreDemand.inwardEdgeSym2_injective axis hn2 hn3 hedge
    apply Subtype.ext
    let ss : ↥(startSlots axis hn2 hT) :=
      ⟨s.1, by simpa [firstStop] using (Finset.mem_sdiff.mp s.2).1⟩
    let st : ↥(startSlots axis hn2 hT) :=
      ⟨t.1, by simpa [firstStop] using (Finset.mem_sdiff.mp t.2).1⟩
    rw [← startSlot_demandOfStartSlot axis hn2 hT ss,
      ← startSlot_demandOfStartSlot axis hn2 hT st]
    exact congrArg (startSlot axis hn2 hT) hq

/-- Merger slots route injectively to physical tree edges through the
cardinality-chosen unmarked starts. -/
noncomputable def mergerSlotTreeEdgeEmbedding :
    (planeChannelForest axis hn2 hT).forest.MergerSlot ↪ ↥T.edgeFinset :=
  (firstStop axis hn2 hT).mergerSlotUnmarkedStartEmbedding.trans
    (unmarkedStartTreeEdgeEmbedding axis hn2 hn3 hT)

/-- Expanded first-stop exits are all roots, so no surviving-root token exists. -/
theorem noSurvivingRoot
    (r : ↥((planeChannelForest axis hn2 hT).forest.roots \
      (planeChannelForest axis hn2 hT).exits)) : False := by
  let x : (firstStop axis hn2 hT).Carrier := r.1
  have hxroot : x ∈ (planeChannelForest axis hn2 hT).forest.roots :=
    (Finset.mem_sdiff.mp r.2).1
  have hxexit : x ∈ (planeChannelForest axis hn2 hT).exits := by
    rw [exits_eq_roots axis hn2 hT]
    exact hxroot
  exact (Finset.mem_sdiff.mp r.2).2 hxexit

/-- Physical tree-edge tokens for every merger or surviving root.  The latter
branch is impossible because expanded forest exits equal roots. -/
noncomputable def terminalTreeEdgeEmbedding :
    ((planeChannelForest axis hn2 hT).forest.MergerSlot ⊕
      ↥((planeChannelForest axis hn2 hT).forest.roots \
        (planeChannelForest axis hn2 hT).exits)) ↪ ↥T.edgeFinset where
  toFun
    | .inl s => mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT s
    | .inr r => False.elim (noSurvivingRoot axis hn2 hT r)
  inj' := by
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · intro hab
      exact congrArg Sum.inl
        ((mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT).injective hab)
    · exact False.elim (noSurvivingRoot axis hn2 hT b)
    · exact False.elim (noSurvivingRoot axis hn2 hT a)
    · exact False.elim (noSurvivingRoot axis hn2 hT a)

/-- Every canonical terminal token is noninternal.  A merger token comes from
an unsupported demand, whose boundary endpoint is outside cotree support; the
surviving-root branch is impossible because all roots are exits. -/
theorem terminalTreeEdgeEmbedding_isNoninternal
    (a : (planeChannelForest axis hn2 hT).forest.MergerSlot ⊕
      ↥((planeChannelForest axis hn2 hT).forest.roots \
        (planeChannelForest axis hn2 hT).exits)) :
    ¬TreeEdgeTokenIsInternal (supportFinset (gridGraph n n \ T))
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT) a := by
  rcases a with s | r
  · intro hinternal
    let u := (firstStop axis hn2 hT).mergerSlotUnmarkedStartEmbedding s
    let q := unsupportedDemandOfUnmarkedStart axis hn2 hT u
    have hsource :
        (CanonicalShoreDemand.boundaryIncidence axis hn2 q.1).1 ∈
          ((terminalTreeEdgeEmbedding axis hn2 hn3 hT) (Sum.inl s)).1 := by
      simp [terminalTreeEdgeEmbedding, mergerSlotTreeEdgeEmbedding,
        unmarkedStartTreeEdgeEmbedding, u, q, GridDirectionalDart.edgeSym2,
        Sym2.mem_iff]
      exact Or.inl rfl
    exact CanonicalShoreDemand.unsupported_boundary_not_mem_support axis hn2 T q
      (hinternal _ hsource)
  · exact False.elim (noSurvivingRoot axis hn2 hT r)

/-- Exits together with all terminal tree-edge tokens recover exactly the
`n + 3` canonical starts. -/
theorem card_exits_add_card_terminalTreeEdgeTokens (hn3 : 3 ≤ n) :
    Fintype.card ↥(planeChannelForest axis hn2 hT).exits +
        Fintype.card ((planeChannelForest axis hn2 hT).forest.MergerSlot ⊕
          ↥((planeChannelForest axis hn2 hT).forest.roots \
            (planeChannelForest axis hn2 hT).exits)) =
      n + 3 := by
  let F := firstStop axis hn2 hT
  have hledger := F.forest.card_leaves_eq_card_roots_add_branchExcess
  rw [F.leaves_eq_demands, F.card_demands, ← F.exits_eq_roots] at hledger
  have hstarts := card_startSlots axis hn2 hT hn3
  change F.starts.card = n + 3 at hstarts
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe,
    ParentForest.card_mergerSlot]
  change F.exits.card +
      (F.forest.branchExcess + (F.forest.roots \ F.exits).card) = n + 3
  rw [← F.exits_eq_roots]
  simp only [Finset.sdiff_self, Finset.card_empty, Nat.add_zero]
  omega

/-- The preferred unresolved residual routing condition.  Canonical expanded
exits reserve their actual outer ports, while only collisions left after the
port and physical tree-edge reservations are routed.  No existence claim is
made. -/
def CanonicalExpandedJointCollisionRouting : Prop :=
  Nonempty (PortAwarePhysicalTreeTokenQuotientRouting
    (exitEmbedding axis hn2 hT)
    (supportFinset (gridGraph n n \ T))
    (terminalTreeEdgeEmbedding axis hn2 hn3 hT))

/-- **Exact capacity equivalence.**  Canonical expanded joint collision routing
exists exactly at the incidence-waste threshold.  This audits the routing API;
it does not prove that the bound holds for every spanning tree. -/
theorem canonicalExpandedJointCollisionRouting_iff_incidenceWaste_ge :
    CanonicalExpandedJointCollisionRouting axis hn2 hn3 hT ↔
      n + 2 ≤ incidenceWaste (gridGraph n n \ T) := by
  let U := supportFinset (gridGraph n n \ T)
  rw [CanonicalExpandedJointCollisionRouting,
    nonempty_portAwarePhysicalTreeTokenQuotientRouting_iff_total_card_le
      (exitEmbedding axis hn2 hT) U
      (terminalTreeEdgeEmbedding axis hn2 hn3 hT)
      (terminalTreeEdgeEmbedding_isNoninternal axis hn2 hn3 hT)]
  have hsource := card_exits_add_card_terminalTreeEdgeTokens axis hn2 hT hn3
  change Fintype.card ↥(firstStop axis hn2 hT).exits +
      Fintype.card ((planeChannelForest axis hn2 hT).forest.MergerSlot ⊕
        ↥((planeChannelForest axis hn2 hT).forest.roots \
          (planeChannelForest axis hn2 hT).exits)) = n + 3 at hsource
  have hports := card_gridCotreeOuterPort_eq_boundaryDeficiencySum hn2 hn2 hT
  have hledger :=
    cotree_incidenceWaste_add_one_eq_boundary_add_internal_add_components hn2 hT
  dsimp only [U] at hledger ⊢
  simp only [Fintype.card_coe, Fintype.card_sum, ParentForest.card_mergerSlot,
    planeChannelForest] at hsource hledger ⊢
  omega

/-- The stricter legacy residual routing condition, retained as a sufficient
condition for the realization-based theorem below.  New results should prefer
`CanonicalExpandedJointCollisionRouting`, which reserves exit ports jointly. -/
def CanonicalExpandedCollisionRouting : Prop :=
  Nonempty (PhysicalTreeTokenQuotientRouting
    (supportFinset (gridGraph n n \ T))
    (terminalTreeEdgeEmbedding axis hn2 hn3 hT))

/-- With no separately counted direct exits, reached expanded-contour exits map
injectively to their existing outer ports. -/
def emptyDirectExitEmbedding :
    (↥(∅ : Finset (CanonicalShoreDemand axis n)) ⊕
      ↥(planeChannelForest axis hn2 hT).exits) ↪ GridCotreeOuterPort T where
  toFun
    | .inl q => False.elim (Finset.notMem_empty q.1 q.2)
    | .inr e => exitEmbedding axis hn2 hT e
  inj' := by
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · exact False.elim (Finset.notMem_empty a.1 a.2)
    · exact False.elim (Finset.notMem_empty a.1 a.2)
    · exact False.elim (Finset.notMem_empty b.1 b.2)
    · intro hab
      exact congrArg Sum.inr ((exitEmbedding axis hn2 hT).injective hab)

/-- Jointly embed the empty direct-exit branch and the pruned canonical forest
into the primal contour ledger.  The port-aware routing reserves expanded
exits, and the outer-port equivalence changes only the boundary summand. -/
noncomputable def jointPrunedRootResourceEmbedding
    (hrouting : CanonicalExpandedJointCollisionRouting axis hn2 hn3 hT) :
    (↥(∅ : Finset (CanonicalShoreDemand axis n)) ⊕
        (planeChannelForest axis hn2 hT).PrunedRootResource) ↪
      PrimalContourResource T (supportFinset (gridGraph n n \ T)) := by
  let C := planeChannelForest axis hn2 hT
  let removeEmpty :
      (↥(∅ : Finset (CanonicalShoreDemand axis n)) ⊕ C.PrunedRootResource) ↪
        (↥C.exits ⊕
          (C.forest.MergerSlot ⊕ ↥(C.forest.roots \ C.exits))) :=
    { toFun := fun
        | Sum.inl q => False.elim (Finset.notMem_empty q.1 q.2)
        | Sum.inr resource => resource
      inj' := by
        intro a b
        rcases a with a | a <;> rcases b with b | b
        · exact False.elim (Finset.notMem_empty a.1 a.2)
        · exact False.elim (Finset.notMem_empty a.1 a.2)
        · exact False.elim (Finset.notMem_empty b.1 b.2)
        · exact congrArg Sum.inr }
  exact removeEmpty.trans
    ((Classical.choice hrouting).resourceEmbedding.trans
      (Equiv.sumCongr
        (gridCotreeOuterPortEquivBoundarySector hn2 hn2 hT)
        (Equiv.refl _)).toEmbedding)

/-- Conditional canonical realization obtained from exactly the residual
physical-token collision routing. -/
noncomputable def gridChannelContourRealization
    (hrouting : CanonicalExpandedCollisionRouting axis hn2 hn3 hT) :
    GridDirectionalDart.GridChannelContourRealization hT where
  Carrier := (firstStop axis hn2 hT).Carrier
  axis := axis
  channels := planeChannelForest axis hn2 hT
  directExits := ∅
  continuingEmbedding :=
    { toFun := fun q => demandEmbedding axis hn2 hn3 hT q.1
      inj' := fun _ _ h => Subtype.ext
        ((demandEmbedding axis hn2 hn3 hT).injective h) }
  demand_subset_leaves := demands_subset_leaves axis hn2 hT
  exits_subset_roots := by
    rw [exits_eq_roots axis hn2 hT]
  exitEmbedding := emptyDirectExitEmbedding axis hn2 hT
  terminalResourceEmbedding := (Classical.choice hrouting).resourceEmbedding

/-- Legacy sufficient result using the stricter non-port-aware residual
routing.  Prefer
`square_grid_tree_universalWaste_of_expandedJointCollisionRouting` below. -/
theorem square_grid_tree_universalWaste_of_expandedCollisionRouting
    {n : Nat} (hn3 : 3 ≤ n)
    (hrouting : ∀ {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
      (hT : IsSpanningSubtree (gridGraph n n) T),
        CanonicalExpandedCollisionRouting .rows (by omega) hn3 hT)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) :=
  (gridChannelContourRealization .rows (by omega) hn3 hT
    (hrouting hT)).incidenceWaste_ge (by omega)

/-- Preferred joint form: port-aware residual routing for every square-grid
spanning tree implies the universal incidence-waste bound. -/
theorem square_grid_tree_universalWaste_of_expandedJointCollisionRouting
    {n : Nat} (hn3 : 3 ≤ n)
    (hrouting : ∀ {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
      (hT : IsSpanningSubtree (gridGraph n n) T),
        CanonicalExpandedJointCollisionRouting .rows (by omega) hn3 hT)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) := by
  apply PlaneChannelForest.incidenceWaste_ge_of_jointChannelContourRoutingWithDirectExits
    (by omega) .rows hT (planeChannelForest .rows (by omega) hT) ∅
    { toFun := fun q => demandEmbedding .rows (by omega) hn3 hT q.1
      inj' := fun _ _ h => Subtype.ext
        ((demandEmbedding .rows (by omega) hn3 hT).injective h) }
    (demands_subset_leaves .rows (by omega) hT)
    (by rw [exits_eq_roots .rows (by omega) hT])
  exact jointPrunedRootResourceEmbedding .rows (by omega) hn3 hT (hrouting hT)

end

end CanonicalExpandedContourForest

end GridGraphs
