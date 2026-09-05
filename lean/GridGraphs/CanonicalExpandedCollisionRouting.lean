import GridGraphs.CanonicalExpandedContourForest
import GridGraphs.GridChannelContourRealization
import GridGraphs.JointChannelContourRouting
import GridGraphs.TerminalCarrierQuotientRouting
import GridGraphs.RankedCarrierQuotient
import GridGraphs.BareCombTransition
import GridGraphs.GridCellBoundaryEdges
import GridGraphs.GridCrosscutCycle
import GridGraphs.GridCornerContourRouting

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

private theorem outerBoundarySide_inwardDirection_injective :
    Function.Injective OuterBoundarySide.inwardDirection := by
  intro a b hab
  cases a <;> cases b <;>
    simp [OuterBoundarySide.inwardDirection] at hab ⊢

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

/-- Merger slots route injectively to physical tree edges through their
canonical orbit-local unmarked starts. -/
noncomputable def mergerSlotTreeEdgeEmbedding :
    (planeChannelForest axis hn2 hT).forest.MergerSlot ↪ ↥T.edgeFinset :=
  (firstStop axis hn2 hT).canonicalMergerSlotUnmarkedStartEmbedding.trans
    (unmarkedStartTreeEdgeEmbedding axis hn2 hn3 hT)

/-! ## Contact-enriched canonical merger tokens -/

/-- A merger token retaining its occurrence label.  The canonical unsupported
demand, oriented inward tree edge, outside endpoint, induced full component,
and attachment orientation below are all deterministic projections of this
token.  Thus enriching the token loses no occurrences and introduces no choice
of a carrier endpoint. -/
structure ContactEnrichedCanonicalMergerToken where
  mergerSlot : (planeChannelForest axis hn2 hT).forest.MergerSlot

/-- The canonical unmarked start owned by an enriched merger token. -/
def ContactEnrichedCanonicalMergerToken.unmarkedStart
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :=
  (firstStop axis hn2 hT).canonicalMergerSlotUnmarkedStartEmbedding
    token.mergerSlot

/-- The unsupported canonical demand represented by the token's unmarked
start. -/
def ContactEnrichedCanonicalMergerToken.unsupportedDemand
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    CanonicalShoreDemand.Unsupported axis hn2 T :=
  unsupportedDemandOfUnmarkedStart axis hn2 hT token.unmarkedStart

/-- The retained, canonically oriented inward tree edge attached at the
outside contact. -/
noncomputable def ContactEnrichedCanonicalMergerToken.inwardDart
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    GridDirectionalDart T :=
  GridDirectionalDart.retainedCanonicalInwardDart axis hn2 hT
    token.unsupportedDemand

/-- Explicit endpoint outside cotree support. -/
def ContactEnrichedCanonicalMergerToken.contact
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    ↥((Finset.univ : Finset (GridVertex n n)) \
      supportFinset (gridGraph n n \ T)) :=
  ⟨token.inwardDart.source, Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _, CanonicalShoreDemand.unsupported_boundary_not_mem_support
      axis hn2 T token.unsupportedDemand⟩⟩

/-- Raw induced full component selected by the explicit outside contact. -/
def ContactEnrichedCanonicalMergerToken.component
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    ((gridGraph n n).induce
      (↑((Finset.univ : Finset (GridVertex n n)) \
        supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))).ConnectedComponent :=
  ((gridGraph n n).induce
    (↑((Finset.univ : Finset (GridVertex n n)) \
      supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))).connectedComponentMk
        token.contact

/-- Attachment orientation at the contact is the canonical inward compass
direction, retained separately from the unordered physical tree edge. -/
def ContactEnrichedCanonicalMergerToken.attachmentOrientation
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) : GridDirection :=
  token.inwardDart.direction

@[simp] theorem ContactEnrichedCanonicalMergerToken.contact_eq_boundaryIncidence
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    token.contact.1 =
      (CanonicalShoreDemand.boundaryIncidence axis hn2
        token.unsupportedDemand.1).1 := rfl

@[simp] theorem ContactEnrichedCanonicalMergerToken.attachmentOrientation_eq
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    token.attachmentOrientation =
      (CanonicalShoreDemand.boundaryIncidence axis hn2
        token.unsupportedDemand.1).2.inwardDirection := rfl

def ContactEnrichedCanonicalMergerToken.boundarySide
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    OuterBoundarySide :=
  (CanonicalShoreDemand.boundaryIncidence axis hn2
    token.unsupportedDemand.1).2

theorem ContactEnrichedCanonicalMergerToken.boundarySide_incidence
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    match token.boundarySide axis hn2 hT with
    | .top => token.contact.1.1.val = 0
    | .bottom => token.contact.1.1.val + 1 = n
    | .left => token.contact.1.2.val = 0
    | .right => token.contact.1.2.val + 1 = n := by
  simpa [ContactEnrichedCanonicalMergerToken.boundarySide] using
    CanonicalShoreDemand.boundaryIncidence_side_incidence axis hn2
      token.unsupportedDemand.1

@[simp] theorem ContactEnrichedCanonicalMergerToken.contact_mem_component
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    token.contact ∈ token.component.supp := by
  change ((gridGraph n n).induce
    (↑((Finset.univ : Finset (GridVertex n n)) \
      supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))).connectedComponentMk
        token.contact = token.component
  rfl

@[simp] theorem ContactEnrichedCanonicalMergerToken.inwardDart_edge
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    token.inwardDart.edgeSym2 =
      (mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT token.mergerSlot).1 := rfl

/-- Contact enrichment is exactly equivalent to the original merger-slot
ledger. -/
def contactEnrichedCanonicalMergerTokenEquiv :
    ContactEnrichedCanonicalMergerToken axis hn2 hT ≃
      (planeChannelForest axis hn2 hT).forest.MergerSlot where
  toFun := ContactEnrichedCanonicalMergerToken.mergerSlot
  invFun := fun mergerSlot => ⟨mergerSlot⟩
  left_inv := by rintro ⟨mergerSlot⟩; rfl
  right_inv _ := rfl

noncomputable instance contactEnrichedCanonicalMergerTokenFintype :
    Fintype (ContactEnrichedCanonicalMergerToken axis hn2 hT) :=
  Fintype.ofEquiv _ (contactEnrichedCanonicalMergerTokenEquiv axis hn2 hT).symm

noncomputable instance contactEnrichedCanonicalMergerTokenDecidableEq :
    DecidableEq (ContactEnrichedCanonicalMergerToken axis hn2 hT) :=
  Classical.decEq _

theorem contactEnrichedCanonicalMergerTokenEquiv_injective :
    Function.Injective
      (contactEnrichedCanonicalMergerTokenEquiv axis hn2 hT) :=
  (contactEnrichedCanonicalMergerTokenEquiv axis hn2 hT).injective

/-- Fixed canonical demand whose expanded slot anchors the contour order. -/
def canonicalContourRankAnchorDemand (hn2 : 2 ≤ n) :
    CanonicalShoreDemand axis n :=
  Sum.inl ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn2⟩

/-- Expanded contour slot used as rank zero for canonical merger ordering. -/
def canonicalContourRankAnchor : GridCompassSlot n n :=
  startSlot axis hn2 hT (canonicalContourRankAnchorDemand axis hn2)

/-- Forward contour rank of a merger token's canonical orbit-local unmarked
start slot. -/
def canonicalMergerForwardRank
    (s : (planeChannelForest axis hn2 hT).forest.MergerSlot) : Nat :=
  forwardCycleRank (GridExpandedContour.equiv (T := T))
    (canonicalContourRankAnchor axis hn2 hT)
    (fun x => GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT
      (canonicalContourRankAnchor axis hn2 hT) x)
    ((firstStop axis hn2 hT).canonicalMergerSlotUnmarkedStartEmbedding s).1

/-- Single-cycle forward rank and the token-to-owner-slot embedding distinguish
canonical merger tokens. -/
theorem canonicalMergerForwardRank_injective :
    Function.Injective (canonicalMergerForwardRank axis hn2 hT) := by
  intro s t hst
  apply (firstStop axis hn2 hT).canonicalMergerSlotUnmarkedStartEmbedding.injective
  apply Subtype.ext
  exact forwardCycleRank_injective (GridExpandedContour.equiv (T := T))
    (canonicalContourRankAnchor axis hn2 hT)
    (fun x => GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT
      (canonicalContourRankAnchor axis hn2 hT) x) hst

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
    let u := (firstStop axis hn2 hT).canonicalMergerSlotUnmarkedStartEmbedding s
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

/-- Every merger edge token is noninternal, as a direct specialization of the
terminal-token statement. -/
theorem mergerSlotTreeEdgeEmbedding_isNoninternal
    (s : (planeChannelForest axis hn2 hT).forest.MergerSlot) :
    ¬TreeEdgeTokenIsInternal (supportFinset (gridGraph n n \ T))
      (mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT) s := by
  simpa [terminalTreeEdgeEmbedding] using
    (terminalTreeEdgeEmbedding_isNoninternal axis hn2 hn3 hT (Sum.inl s))

/-- The explicit outside contact selects the same raw induced component as the
legacy arbitrary outside-endpoint choice. -/
theorem contactEnrichedCanonicalMergerToken_component_compatible
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    token.component =
      noninternalTreeEdgeTokenComponent
        (supportFinset (gridGraph n n \ T))
        (mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT)
        ⟨token.mergerSlot,
          mergerSlotTreeEdgeEmbedding_isNoninternal axis hn2 hn3 hT
            token.mergerSlot⟩ := by
  classical
  let U := supportFinset (gridGraph n n \ T)
  let edgeEmbedding := mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT
  let outside : ∃ v, v ∈ (edgeEmbedding token.mergerSlot).1 ∧ v ∉ U := by
    by_contra hnone
    push_neg at hnone
    exact (mergerSlotTreeEdgeEmbedding_isNoninternal
      axis hn2 hn3 hT token.mergerSlot) (fun v hv => hnone v hv)
  let chosen := Classical.choose outside
  have hchosen := Classical.choose_spec outside
  let chosenVertex : ↥((Finset.univ : Finset (GridVertex n n)) \ U) :=
    ⟨chosen, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hchosen.2⟩⟩
  change ((gridGraph n n).induce
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) : Set (GridVertex n n))).connectedComponentMk
        token.contact =
    ((gridGraph n n).induce
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) : Set (GridVertex n n))).connectedComponentMk
        chosenVertex
  rw [SimpleGraph.ConnectedComponent.eq]
  by_cases heq : chosenVertex = token.contact
  · rw [heq]
  · apply SimpleGraph.Adj.reachable
    change (gridGraph n n).Adj token.contact.1 chosenVertex.1
    have hedge : token.inwardDart.edgeSym2 =
        (edgeEmbedding token.mergerSlot).1 := by
      exact token.inwardDart_edge axis hn2 hn3 hT
    have hchosenEdge : chosen ∈ token.inwardDart.edgeSym2 := by
      rw [hedge]
      exact hchosen.1
    rw [GridDirectionalDart.edgeSym2, Sym2.mem_iff] at hchosenEdge
    rcases hchosenEdge with hsource | htarget
    · apply (heq ?_).elim
      apply Subtype.ext
      simpa [chosenVertex, ContactEnrichedCanonicalMergerToken.contact] using
        hsource
    · have hadj := hT.le token.inwardDart.adj
      simpa [chosenVertex, ContactEnrichedCanonicalMergerToken.contact,
        htarget] using hadj

/-- Preserved-component carrier of a canonical merger edge token. -/
def canonicalMergerTokenCarrier
    (s : (planeChannelForest axis hn2 hT).forest.MergerSlot) :=
  noninternalTreeEdgeTokenComponent
    (supportFinset (gridGraph n n \ T))
    (mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT)
    ⟨s, mergerSlotTreeEdgeEmbedding_isNoninternal axis hn2 hn3 hT s⟩

/-- Contact-enriched carrier map, with no arbitrary endpoint selection. -/
def contactEnrichedCanonicalMergerCarrier
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :=
  token.component

theorem contactEnrichedCanonicalMergerCarrier_compatible
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    contactEnrichedCanonicalMergerCarrier axis hn2 hT token =
      canonicalMergerTokenCarrier axis hn2 hn3 hT token.mergerSlot :=
  contactEnrichedCanonicalMergerToken_component_compatible axis hn2 hn3 hT token

/-- Contour rank transported without loss to contact-enriched tokens. -/
def contactEnrichedCanonicalMergerRank
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) : Nat :=
  canonicalMergerForwardRank axis hn2 hT token.mergerSlot

theorem contactEnrichedCanonicalMergerRank_injective :
    Function.Injective (contactEnrichedCanonicalMergerRank axis hn2 hT) := by
  intro a b hab
  apply (contactEnrichedCanonicalMergerTokenEquiv axis hn2 hT).injective
  exact canonicalMergerForwardRank_injective axis hn2 hT hab

/-- Contact-enriched merger occurrences other than the first contour-ranked
contact in their raw induced component. -/
abbrev RankedContactEnrichedCarrierCollision
    (axis : ShoreSweepAxis) (hn2 : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :=
  RankedCarrierCollision
    (contactEnrichedCanonicalMergerCarrier axis hn2 hT)
    (contactEnrichedCanonicalMergerRank axis hn2 hT)

/-- Same-component contacts strictly preceding `current` in contour rank. -/
def lowerRankedSameComponentContacts
    (current : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    Finset (ContactEnrichedCanonicalMergerToken axis hn2 hT) :=
  Finset.univ.filter fun previous =>
    previous.component = current.component ∧
      contactEnrichedCanonicalMergerRank axis hn2 hT previous <
        contactEnrichedCanonicalMergerRank axis hn2 hT current

theorem lowerRankedSameComponentContacts_nonempty
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT) :
    (lowerRankedSameComponentContacts axis hn2 hT collision.1).Nonempty := by
  let carrier := contactEnrichedCanonicalMergerCarrier axis hn2 hT
  let rank := contactEnrichedCanonicalMergerRank axis hn2 hT
  let q := carrierQuotientMk carrier collision.1
  let representative := rankedCarrierRepresentative carrier rank q
  have hrepQ : carrierQuotientMk carrier representative = q :=
    carrierQuotientMk_rankedCarrierRepresentative carrier rank q
  have hcurrentQ : carrierQuotientMk carrier collision.1 = q := rfl
  have hcarrier : carrier representative = carrier collision.1 := by
    exact Quotient.exact (hrepQ.trans hcurrentQ.symm)
  have hle : rank representative ≤ rank collision.1 :=
    rankedCarrierRepresentative_rank_le carrier rank q hcurrentQ
  have hne : rank representative ≠ rank collision.1 := by
    intro heq
    exact collision.2
      ((contactEnrichedCanonicalMergerRank_injective axis hn2 hT heq).symm)
  exact ⟨representative, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hcarrier, Nat.lt_of_le_of_ne hle hne⟩⟩

/-- The immediate previous same-component contact: maximal contour rank among
all strictly lower contacts in the same raw component. -/
noncomputable def rankedCarrierGapPredecessor
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT) :
    ContactEnrichedCanonicalMergerToken axis hn2 hT :=
  Classical.choose (Finset.exists_max_image
    (lowerRankedSameComponentContacts axis hn2 hT collision.1)
    (contactEnrichedCanonicalMergerRank axis hn2 hT)
    (lowerRankedSameComponentContacts_nonempty axis hn2 hT collision))

theorem rankedCarrierGapPredecessor_mem
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT) :
    rankedCarrierGapPredecessor axis hn2 hT collision ∈
      lowerRankedSameComponentContacts axis hn2 hT collision.1 :=
  (Classical.choose_spec (Finset.exists_max_image
    (lowerRankedSameComponentContacts axis hn2 hT collision.1)
    (contactEnrichedCanonicalMergerRank axis hn2 hT)
    (lowerRankedSameComponentContacts_nonempty axis hn2 hT collision))).1

theorem rankedCarrierGapPredecessor_component
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT) :
    (rankedCarrierGapPredecessor axis hn2 hT collision).component =
      collision.1.component :=
  (Finset.mem_filter.mp
    (rankedCarrierGapPredecessor_mem axis hn2 hT collision)).2.1

theorem rankedCarrierGapPredecessor_rank_lt
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT) :
    contactEnrichedCanonicalMergerRank axis hn2 hT
        (rankedCarrierGapPredecessor axis hn2 hT collision) <
      contactEnrichedCanonicalMergerRank axis hn2 hT collision.1 :=
  (Finset.mem_filter.mp
    (rankedCarrierGapPredecessor_mem axis hn2 hT collision)).2.2

theorem rankedCarrierGapPredecessor_rank_maximal
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT)
    {previous : ContactEnrichedCanonicalMergerToken axis hn2 hT}
    (hprevious : previous ∈
      lowerRankedSameComponentContacts axis hn2 hT collision.1) :
    contactEnrichedCanonicalMergerRank axis hn2 hT previous ≤
      contactEnrichedCanonicalMergerRank axis hn2 hT
        (rankedCarrierGapPredecessor axis hn2 hT collision) :=
  (Classical.choose_spec (Finset.exists_max_image
    (lowerRankedSameComponentContacts axis hn2 hT collision.1)
    (contactEnrichedCanonicalMergerRank axis hn2 hT)
    (lowerRankedSameComponentContacts_nonempty axis hn2 hT collision))).2
      previous hprevious

/-- Contour consecutiveness: no contact in the same component has rank strictly
between the selected predecessor and current contact. -/
theorem rankedCarrierGap_no_intermediate_contour_contact
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT)
    (middle : ContactEnrichedCanonicalMergerToken axis hn2 hT)
    (hcomponent : middle.component = collision.1.component)
    (hleft : contactEnrichedCanonicalMergerRank axis hn2 hT
        (rankedCarrierGapPredecessor axis hn2 hT collision) <
      contactEnrichedCanonicalMergerRank axis hn2 hT middle)
    (hright : contactEnrichedCanonicalMergerRank axis hn2 hT middle <
      contactEnrichedCanonicalMergerRank axis hn2 hT collision.1) : False := by
  have hmem : middle ∈
      lowerRankedSameComponentContacts axis hn2 hT collision.1 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomponent, hright⟩
  have hmax := rankedCarrierGapPredecessor_rank_maximal
    axis hn2 hT collision hmem
  omega

/-- The maximal lower same-component predecessor is unique. -/
theorem rankedCarrierGapPredecessor_unique
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT)
    (previous : ContactEnrichedCanonicalMergerToken axis hn2 hT)
    (hmem : previous ∈
      lowerRankedSameComponentContacts axis hn2 hT collision.1)
    (hmax : ∀ other ∈
      lowerRankedSameComponentContacts axis hn2 hT collision.1,
      contactEnrichedCanonicalMergerRank axis hn2 hT other ≤
        contactEnrichedCanonicalMergerRank axis hn2 hT previous) :
    previous = rankedCarrierGapPredecessor axis hn2 hT collision := by
  apply contactEnrichedCanonicalMergerRank_injective axis hn2 hT
  apply Nat.le_antisymm
  · exact rankedCarrierGapPredecessor_rank_maximal axis hn2 hT collision hmem
  · exact hmax _ (rankedCarrierGapPredecessor_mem axis hn2 hT collision)

/-- Consecutive same-component contact pair, retaining both contact labels and
the contour-order maximality proof. -/
structure RankedCarrierGapWitness where
  current : RankedContactEnrichedCarrierCollision axis hn2 hT
  previous : ContactEnrichedCanonicalMergerToken axis hn2 hT
  previous_eq : previous = rankedCarrierGapPredecessor axis hn2 hT current

/-- Canonical gap selected by a ranked collision. -/
def rankedCarrierGapWitness
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT) :
    RankedCarrierGapWitness axis hn2 hT where
  current := collision
  previous := rankedCarrierGapPredecessor axis hn2 hT collision
  previous_eq := rfl

/-- No collision information is lost by passing to its predecessor/current
contact gap. -/
def rankedCarrierCollisionGapEmbedding :
    RankedContactEnrichedCarrierCollision axis hn2 hT ↪
      (ContactEnrichedCanonicalMergerToken axis hn2 hT ×
        ContactEnrichedCanonicalMergerToken axis hn2 hT) where
  toFun collision :=
    (rankedCarrierGapPredecessor axis hn2 hT collision, collision.1)
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg Prod.snd hab

/-- The two explicit contacts of a ranked carrier gap belong to one straight
induced full component. -/
theorem rankedCarrierGap_contacts_same_row_or_column
    (gap : RankedCarrierGapWitness axis hn2 hT) :
    gap.previous.contact.1.1 = gap.current.1.contact.1.1 ∨
      gap.previous.contact.1.2 = gap.current.1.contact.1.2 := by
  rw [gap.previous_eq]
  let C := gap.current.1.component
  have hp : (rankedCarrierGapPredecessor axis hn2 hT gap.current).contact ∈ C.supp := by
    have hp' := ContactEnrichedCanonicalMergerToken.contact_mem_component
      axis hn2 hT (rankedCarrierGapPredecessor axis hn2 hT gap.current)
    rw [rankedCarrierGapPredecessor_component axis hn2 hT gap.current] at hp'
    exact hp'
  have hc : gap.current.1.contact ∈ C.supp :=
    ContactEnrichedCanonicalMergerToken.contact_mem_component axis hn2 hT _
  rcases cotree_full_component_straight hT C with ⟨row, hrow⟩ | ⟨column, hcolumn⟩
  · exact Or.inl ((hrow _ hp).trans (hrow _ hc).symm)
  · exact Or.inr ((hcolumn _ hp).trans (hcolumn _ hc).symm)

/-- Horizontal interval closure between the two contacts of a ranked gap. -/
theorem rankedCarrierGap_horizontal_intermediate_mem
    (gap : RankedCarrierGapWitness axis hn2 hT)
    (hrow : gap.previous.contact.1.1 = gap.current.1.contact.1.1)
    (column : Fin n)
    (hbetween :
      (gap.previous.contact.1.2.val ≤ column.val ∧
        column.val ≤ gap.current.1.contact.1.2.val) ∨
      (gap.current.1.contact.1.2.val ≤ column.val ∧
        column.val ≤ gap.previous.contact.1.2.val)) :
    ∃ contact : ↥(↑((Finset.univ : Finset (GridVertex n n)) \
        supportFinset (gridGraph n n \ T)) : Set (GridVertex n n)),
      contact.1 = (gap.previous.contact.1.1, column) ∧
        contact ∈ gap.current.1.component.supp := by
  rw [gap.previous_eq] at hrow hbetween ⊢
  obtain ⟨hfree, hmem⟩ := induced_forced_connectedComponent_horizontal_interval
    (grid_tree_complement_forcedEdgeGraph_isAcyclic hT)
    gap.current.1.component
    (u := (rankedCarrierGapPredecessor axis hn2 hT gap.current).contact)
    (v := gap.current.1.contact)
    (c := column) (by
      have hp := ContactEnrichedCanonicalMergerToken.contact_mem_component
        axis hn2 hT (rankedCarrierGapPredecessor axis hn2 hT gap.current)
      rw [rankedCarrierGapPredecessor_component axis hn2 hT gap.current] at hp
      exact hp)
    (ContactEnrichedCanonicalMergerToken.contact_mem_component axis hn2 hT _)
    hrow hbetween
  exact ⟨⟨_, hfree⟩, rfl, hmem⟩

/-- Vertical interval closure between the two contacts of a ranked gap. -/
theorem rankedCarrierGap_vertical_intermediate_mem
    (gap : RankedCarrierGapWitness axis hn2 hT)
    (hcolumn : gap.previous.contact.1.2 = gap.current.1.contact.1.2)
    (row : Fin n)
    (hbetween :
      (gap.previous.contact.1.1.val ≤ row.val ∧
        row.val ≤ gap.current.1.contact.1.1.val) ∨
      (gap.current.1.contact.1.1.val ≤ row.val ∧
        row.val ≤ gap.previous.contact.1.1.val)) :
    ∃ contact : ↥(↑((Finset.univ : Finset (GridVertex n n)) \
        supportFinset (gridGraph n n \ T)) : Set (GridVertex n n)),
      contact.1 = (row, gap.previous.contact.1.2) ∧
        contact ∈ gap.current.1.component.supp := by
  rw [gap.previous_eq] at hcolumn hbetween ⊢
  obtain ⟨hfree, hmem⟩ := induced_forced_connectedComponent_vertical_interval
    (grid_tree_complement_forcedEdgeGraph_isAcyclic hT)
    gap.current.1.component
    (u := (rankedCarrierGapPredecessor axis hn2 hT gap.current).contact)
    (v := gap.current.1.contact)
    (r := row) (by
      have hp := ContactEnrichedCanonicalMergerToken.contact_mem_component
        axis hn2 hT (rankedCarrierGapPredecessor axis hn2 hT gap.current)
      rw [rankedCarrierGapPredecessor_component axis hn2 hT gap.current] at hp
      exact hp)
    (ContactEnrichedCanonicalMergerToken.contact_mem_component axis hn2 hT _)
    hcolumn hbetween
  exact ⟨⟨_, hfree⟩, rfl, hmem⟩

/-- Spatial order of two contacts in one straight component.  It is retained
separately from contour rank because the latter is cyclic and anchored at an
expanded slot rather than at an endpoint of each component interval. -/
inductive RankedCarrierGapSpatialOrder
    (gap : RankedCarrierGapWitness axis hn2 hT) : Prop where
  | coincident
      (hcontact : gap.previous.contact.1 = gap.current.1.contact.1)
  | horizontalForward
      (hrow : gap.previous.contact.1.1 = gap.current.1.contact.1.1)
      (hcol : gap.previous.contact.1.2.val < gap.current.1.contact.1.2.val)
  | horizontalReverse
      (hrow : gap.previous.contact.1.1 = gap.current.1.contact.1.1)
      (hcol : gap.current.1.contact.1.2.val < gap.previous.contact.1.2.val)
  | verticalForward
      (hcol : gap.previous.contact.1.2 = gap.current.1.contact.1.2)
      (hrow : gap.previous.contact.1.1.val < gap.current.1.contact.1.1.val)
  | verticalReverse
      (hcol : gap.previous.contact.1.2 = gap.current.1.contact.1.2)
      (hrow : gap.current.1.contact.1.1.val < gap.previous.contact.1.1.val)

/-- Every contour-consecutive carrier gap has an explicit spatial
characterization.  Both forward and reverse cases remain possible at this
level; no false agreement between cyclic contour order and linear component
order is asserted. -/
theorem rankedCarrierGap_spatialOrder
    (gap : RankedCarrierGapWitness axis hn2 hT) :
    RankedCarrierGapSpatialOrder axis hn2 hT gap := by
  by_cases heq : gap.previous.contact.1 = gap.current.1.contact.1
  · exact .coincident heq
  rcases rankedCarrierGap_contacts_same_row_or_column axis hn2 hT gap with
    hrow | hcol
  · have hne : gap.previous.contact.1.2.val ≠
        gap.current.1.contact.1.2.val := by
      intro hval
      apply heq
      apply Prod.ext hrow
      exact Fin.ext hval
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact .horizontalForward hrow hlt
    · exact .horizontalReverse hrow hgt
  · have hne : gap.previous.contact.1.1.val ≠
        gap.current.1.contact.1.1.val := by
      intro hval
      apply heq
      apply Prod.ext
      · exact Fin.ext hval
      · exact hcol
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact .verticalForward hcol hlt
    · exact .verticalReverse hcol hgt

/-- Coincident contact vertices still retain their distinct attachment
orientations.  Otherwise injectivity of canonical boundary incidences would
identify the two merger tokens. -/
theorem rankedCarrierGap_attachmentOrientation_ne_of_contact_eq
    (gap : RankedCarrierGapWitness axis hn2 hT)
    (hcontact : gap.previous.contact.1 = gap.current.1.contact.1) :
    gap.previous.attachmentOrientation ≠
      gap.current.1.attachmentOrientation := by
  intro horientation
  have hincidence :
      CanonicalShoreDemand.boundaryIncidence axis hn2
          gap.previous.unsupportedDemand.1 =
        CanonicalShoreDemand.boundaryIncidence axis hn2
          gap.current.1.unsupportedDemand.1 := by
    apply Prod.ext
    · simpa [ContactEnrichedCanonicalMergerToken.contact,
        ContactEnrichedCanonicalMergerToken.inwardDart] using hcontact
    · apply outerBoundarySide_inwardDirection_injective
      simpa [ContactEnrichedCanonicalMergerToken.attachmentOrientation,
        ContactEnrichedCanonicalMergerToken.inwardDart] using horientation
  have hdemand := CanonicalShoreDemand.boundaryIncidence_injective axis hn2 hincidence
  have hstart : gap.previous.unmarkedStart = gap.current.1.unmarkedStart := by
    apply Subtype.ext
    let previousStart : ↥(startSlots axis hn2 hT) :=
      ⟨gap.previous.unmarkedStart.1, by
        simpa [firstStop] using
          (Finset.mem_sdiff.mp gap.previous.unmarkedStart.2).1⟩
    let currentStart : ↥(startSlots axis hn2 hT) :=
      ⟨gap.current.1.unmarkedStart.1, by
        simpa [firstStop] using
          (Finset.mem_sdiff.mp gap.current.1.unmarkedStart.2).1⟩
    rw [← startSlot_demandOfStartSlot axis hn2 hT previousStart,
      ← startSlot_demandOfStartSlot axis hn2 hT currentStart]
    exact congrArg (startSlot axis hn2 hT) hdemand
  have hslot := (firstStop axis hn2 hT).canonicalMergerSlotUnmarkedStartEmbedding.injective
    hstart
  have htoken : gap.previous = gap.current.1 := by
    apply (contactEnrichedCanonicalMergerTokenEquiv axis hn2 hT).injective
    exact hslot
  rw [gap.previous_eq] at htoken
  have hrank := congrArg
    (contactEnrichedCanonicalMergerRank axis hn2 hT) htoken
  exact (Nat.ne_of_lt (rankedCarrierGapPredecessor_rank_lt
    axis hn2 hT gap.current)) hrank

/-! ## Spatial refinement and boundary-cell gaps -/

/-- Coordinate rectangle between the contour predecessor and current contact.
Straightness later reduces this rectangle to a row or column interval. -/
def rankedCarrierGapSpatialCandidates
    (gap : RankedCarrierGapWitness axis hn2 hT) :
    Finset (ContactEnrichedCanonicalMergerToken axis hn2 hT) :=
  Finset.univ.filter fun token =>
    token.component = gap.current.1.component ∧
    token.contact.1 ≠ gap.current.1.contact.1 ∧
    ((gap.previous.contact.1.1.val ≤ token.contact.1.1.val ∧
        token.contact.1.1.val ≤ gap.current.1.contact.1.1.val) ∨
      (gap.current.1.contact.1.1.val ≤ token.contact.1.1.val ∧
        token.contact.1.1.val ≤ gap.previous.contact.1.1.val)) ∧
    ((gap.previous.contact.1.2.val ≤ token.contact.1.2.val ∧
        token.contact.1.2.val ≤ gap.current.1.contact.1.2.val) ∨
      (gap.current.1.contact.1.2.val ≤ token.contact.1.2.val ∧
        token.contact.1.2.val ≤ gap.previous.contact.1.2.val))

def contactGridDistance
    (a b : ContactEnrichedCanonicalMergerToken axis hn2 hT) : Nat :=
  Nat.dist a.contact.1.1.val b.contact.1.1.val +
    Nat.dist a.contact.1.2.val b.contact.1.2.val

/-! ### Main component-local spatial order -/

def outerBoundarySideTie : OuterBoundarySide → Nat
  | .top => 0
  | .right => 1
  | .bottom => 2
  | .left => 3

/-- Total spatial key: clockwise perimeter position with the boundary-side
incidence as a corner tie-break. -/
def contactSpatialKey
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) : Nat :=
  4 * gridBoundaryIndex token.contact.1 +
    outerBoundarySideTie (token.boundarySide axis hn2 hT)

private theorem outerBoundarySideTie_injective :
    Function.Injective outerBoundarySideTie := by
  intro a b h
  cases a <;> cases b <;> simp_all [outerBoundarySideTie]

private def liesOnOuterBoundarySide (side : OuterBoundarySide)
    (v : GridVertex n n) : Prop :=
  match side with
  | .top => v.1.val = 0
  | .bottom => v.1.val + 1 = n
  | .left => v.2.val = 0
  | .right => v.2.val + 1 = n

private theorem gridBoundaryIndex_injective_of_side
    {v w : GridVertex n n} (side : OuterBoundarySide)
    (hn2 : 2 ≤ n)
    (hv : liesOnOuterBoundarySide side v)
    (hw : liesOnOuterBoundarySide side w)
    (hindex : gridBoundaryIndex v = gridBoundaryIndex w) : v = w := by
  cases side <;>
    simp only [liesOnOuterBoundarySide] at hv hw <;>
    unfold gridBoundaryIndex gridBoundaryLength at hindex <;>
    split_ifs at hindex <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem contactSpatialKey_injective :
    Function.Injective (contactSpatialKey axis hn2 hT) := by
  intro a b hab
  have hindex : gridBoundaryIndex a.contact.1 =
      gridBoundaryIndex b.contact.1 := by
    unfold contactSpatialKey at hab
    have ha : outerBoundarySideTie (a.boundarySide axis hn2 hT) < 4 := by
      cases a.boundarySide axis hn2 hT <;> decide
    have hb : outerBoundarySideTie (b.boundarySide axis hn2 hT) < 4 := by
      cases b.boundarySide axis hn2 hT <;> decide
    omega
  have htie : outerBoundarySideTie (a.boundarySide axis hn2 hT) =
      outerBoundarySideTie (b.boundarySide axis hn2 hT) := by
    unfold contactSpatialKey at hab
    omega
  have hside := outerBoundarySideTie_injective htie
  have hvertex : a.contact.1 = b.contact.1 := by
    have ha := a.boundarySide_incidence axis hn2 hT
    have hb := b.boundarySide_incidence axis hn2 hT
    rw [hside] at ha
    exact gridBoundaryIndex_injective_of_side
      (b.boundarySide axis hn2 hT) hn2 ha hb hindex
  have hincidence : CanonicalShoreDemand.boundaryIncidence axis hn2
        a.unsupportedDemand.1 =
      CanonicalShoreDemand.boundaryIncidence axis hn2
        b.unsupportedDemand.1 := by
    exact Prod.ext (by simpa using hvertex) hside
  have hdemand := CanonicalShoreDemand.boundaryIncidence_injective axis hn2 hincidence
  have hstart : a.unmarkedStart = b.unmarkedStart := by
    apply Subtype.ext
    let sa : ↥(startSlots axis hn2 hT) :=
      ⟨a.unmarkedStart.1, by simpa [firstStop] using
        (Finset.mem_sdiff.mp a.unmarkedStart.2).1⟩
    let sb : ↥(startSlots axis hn2 hT) :=
      ⟨b.unmarkedStart.1, by simpa [firstStop] using
        (Finset.mem_sdiff.mp b.unmarkedStart.2).1⟩
    rw [← startSlot_demandOfStartSlot axis hn2 hT sa,
      ← startSlot_demandOfStartSlot axis hn2 hT sb]
    exact congrArg (startSlot axis hn2 hT) hdemand
  apply (contactEnrichedCanonicalMergerTokenEquiv axis hn2 hT).injective
  exact (firstStop axis hn2 hT).canonicalMergerSlotUnmarkedStartEmbedding.injective
    hstart

/-- All enriched occurrences carried by one raw component. -/
abbrev ContactRawComponent
    {n : Nat} {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj] :=
  ((gridGraph n n).induce
    (↑((Finset.univ : Finset (GridVertex n n)) \
      supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))).ConnectedComponent

abbrev ComponentContact
    (component : ContactRawComponent (T := T)) :=
  {token : ContactEnrichedCanonicalMergerToken axis hn2 hT //
    token.component = component}

def componentContactCarrier
    {component : ContactRawComponent (T := T)}
    (_ : ComponentContact axis hn2 hT component) : Unit := ()

def componentContourRank
    {component : ContactRawComponent (T := T)}
    (token : ComponentContact axis hn2 hT component) : Nat :=
  contactEnrichedCanonicalMergerRank axis hn2 hT token.1

def componentSpatialRank
    {component : ContactRawComponent (T := T)}
    (token : ComponentContact axis hn2 hT component) : Nat :=
  contactSpatialKey axis hn2 hT token.1

theorem componentContourRank_injective
    {component : ContactRawComponent (T := T)} :
    Function.Injective (componentContourRank axis hn2 hT
      (component := component)) := by
  intro a b h
  exact Subtype.ext (contactEnrichedCanonicalMergerRank_injective axis hn2 hT h)

theorem componentSpatialRank_injective
    {component : ContactRawComponent (T := T)} :
    Function.Injective (componentSpatialRank axis hn2 hT
      (component := component)) := by
  intro a b h
  exact Subtype.ext (contactSpatialKey_injective axis hn2 hT h)

abbrev ComponentContourCollision
    (component : ContactRawComponent (T := T)) :=
  RankedCarrierCollision
    (componentContactCarrier axis hn2 hT (component := component))
    (componentContourRank axis hn2 hT (component := component))

/-- The `q - 1` consecutive incidence gaps in component-local spatial order. -/
abbrev ComponentSpatialGap
    (component : ContactRawComponent (T := T)) :=
  RankedCarrierCollision
    (componentContactCarrier axis hn2 hT (component := component))
    (componentSpatialRank axis hn2 hT (component := component))

/-- Both local ledgers have exactly `q - 1` elements because they differ only
in the injective rank used to select the unique representative of the constant
carrier class. -/
theorem card_componentContourCollision_eq_card_componentSpatialGap
    (component : ContactRawComponent (T := T)) :
    Fintype.card (ComponentContourCollision axis hn2 hT component) =
      Fintype.card (ComponentSpatialGap axis hn2 hT component) := by
  rw [card_rankedCarrierCollision_eq_card_carrierCollision,
    card_rankedCarrierCollision_eq_card_carrierCollision]

/-- Component-local replacement of contour residual occurrences by consecutive
spatial incidence gaps.  This is finite local reindexing, not capacity. -/
noncomputable def componentContourCollisionEquivSpatialGap
    (component : ContactRawComponent (T := T)) :
    ComponentContourCollision axis hn2 hT component ≃
      ComponentSpatialGap axis hn2 hT component :=
  Fintype.equivOfCardEq
    (card_componentContourCollision_eq_card_componentSpatialGap
      axis hn2 hT component)

def lowerSpatialComponentContacts
    {component : ContactRawComponent (T := T)}
    (current : ComponentContact axis hn2 hT component) :
    Finset (ComponentContact axis hn2 hT component) :=
  Finset.univ.filter fun previous =>
    componentSpatialRank axis hn2 hT previous <
      componentSpatialRank axis hn2 hT current

theorem lowerSpatialComponentContacts_nonempty
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component) :
    (lowerSpatialComponentContacts axis hn2 hT gap.1).Nonempty := by
  let carrier := componentContactCarrier axis hn2 hT (component := component)
  let rank := componentSpatialRank axis hn2 hT (component := component)
  let q := carrierQuotientMk carrier gap.1
  let representative := rankedCarrierRepresentative carrier rank q
  have hle : rank representative ≤ rank gap.1 :=
    rankedCarrierRepresentative_rank_le carrier rank q rfl
  have hne : rank representative ≠ rank gap.1 := by
    intro heq
    exact gap.2 ((componentSpatialRank_injective axis hn2 hT heq).symm)
  exact ⟨representative, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Nat.lt_of_le_of_ne hle hne⟩⟩

/-- Immediate predecessor of a local spatial-gap label. -/
noncomputable def componentSpatialGapPredecessor
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component) :
    ComponentContact axis hn2 hT component :=
  Classical.choose (Finset.exists_max_image
    (lowerSpatialComponentContacts axis hn2 hT gap.1)
    (componentSpatialRank axis hn2 hT (component := component))
    (lowerSpatialComponentContacts_nonempty axis hn2 hT gap))

theorem componentSpatialGapPredecessor_mem
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component) :
    componentSpatialGapPredecessor axis hn2 hT gap ∈
      lowerSpatialComponentContacts axis hn2 hT gap.1 :=
  (Classical.choose_spec (Finset.exists_max_image
    (lowerSpatialComponentContacts axis hn2 hT gap.1)
    (componentSpatialRank axis hn2 hT (component := component))
    (lowerSpatialComponentContacts_nonempty axis hn2 hT gap))).1

theorem componentSpatialGapPredecessor_rank_lt
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component) :
    componentSpatialRank axis hn2 hT
        (componentSpatialGapPredecessor axis hn2 hT gap) <
      componentSpatialRank axis hn2 hT gap.1 :=
  (Finset.mem_filter.mp
    (componentSpatialGapPredecessor_mem axis hn2 hT gap)).2

theorem componentSpatialGapPredecessor_rank_maximal
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component)
    {previous : ComponentContact axis hn2 hT component}
    (hprevious : previous ∈
      lowerSpatialComponentContacts axis hn2 hT gap.1) :
    componentSpatialRank axis hn2 hT previous ≤
      componentSpatialRank axis hn2 hT
        (componentSpatialGapPredecessor axis hn2 hT gap) :=
  (Classical.choose_spec (Finset.exists_max_image
    (lowerSpatialComponentContacts axis hn2 hT gap.1)
    (componentSpatialRank axis hn2 hT (component := component))
    (lowerSpatialComponentContacts_nonempty axis hn2 hT gap))).2
      previous hprevious

theorem componentSpatialGap_no_intermediate_contact
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component)
    (middle : ComponentContact axis hn2 hT component)
    (hleft : componentSpatialRank axis hn2 hT
        (componentSpatialGapPredecessor axis hn2 hT gap) <
      componentSpatialRank axis hn2 hT middle)
    (hright : componentSpatialRank axis hn2 hT middle <
      componentSpatialRank axis hn2 hT gap.1) : False := by
  have hmem : middle ∈ lowerSpatialComponentContacts axis hn2 hT gap.1 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hright⟩
  exact (Nat.not_lt_of_ge
    (componentSpatialGapPredecessor_rank_maximal axis hn2 hT gap hmem)) hleft

/-! ### Exact duplicated-corner defect -/

/-- The one occurrence-labelled local gap whose two incidence labels occupy the
same corner vertex. The original current occurrence is retained. -/
abbrev DuplicatedCornerOverlapDebt
    (component : ContactRawComponent (T := T)) :=
  {gap : ComponentSpatialGap axis hn2 hT component //
    (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1 =
      gap.1.1.contact.1}

private theorem canonicalDemandPair_exact_duplicated_corner
    (p q : CanonicalShoreDemand axis n)
    (hv : (CanonicalShoreDemand.boundaryIncidence axis hn2 p).1 =
      (CanonicalShoreDemand.boundaryIncidence axis hn2 q).1)
    (hs : outerBoundarySideTie
        (CanonicalShoreDemand.boundaryIncidence axis hn2 p).2 <
      outerBoundarySideTie
        (CanonicalShoreDemand.boundaryIncidence axis hn2 q).2) :
    (axis = .rows ∧
        (CanonicalShoreDemand.boundaryIncidence axis hn2 p).2 = .bottom ∧
        (CanonicalShoreDemand.boundaryIncidence axis hn2 q).2 = .left) ∨
    (axis = .columns ∧
        (CanonicalShoreDemand.boundaryIncidence axis hn2 p).2 = .top ∧
        (CanonicalShoreDemand.boundaryIncidence axis hn2 q).2 = .right) := by
  have hvrow := congrArg (fun v : GridVertex n n => v.1.val) hv
  have hvcol := congrArg (fun v : GridVertex n n => v.2.val) hv
  cases axis with
  | rows =>
      left
      refine ⟨rfl, ?_⟩
      rcases p with p | p <;> rcases q with q | q
      · simp [CanonicalShoreDemand.boundaryIncidence,
          outerBoundarySideTie] at hs
      · fin_cases q <;>
          simp [CanonicalShoreDemand.boundaryIncidence,
            outerBoundarySideTie] at hvrow hvcol hs ⊢
      · fin_cases p <;>
          simp [CanonicalShoreDemand.boundaryIncidence,
            outerBoundarySideTie] at hvrow hvcol hs ⊢ <;> omega
      · fin_cases p <;> fin_cases q <;>
          simp [CanonicalShoreDemand.boundaryIncidence,
            outerBoundarySideTie] at hvrow hvcol hs ⊢ <;> omega
  | columns =>
      right
      refine ⟨rfl, ?_⟩
      rcases p with p | p <;> rcases q with q | q
      · simp [CanonicalShoreDemand.boundaryIncidence,
          outerBoundarySideTie] at hs
      · fin_cases q <;>
          simp [CanonicalShoreDemand.boundaryIncidence,
            outerBoundarySideTie] at hvrow hvcol hs ⊢ <;> omega
      · fin_cases p <;>
          simp [CanonicalShoreDemand.boundaryIncidence,
            outerBoundarySideTie] at hvrow hvcol hs ⊢
      · fin_cases p <;> fin_cases q <;>
          simp [CanonicalShoreDemand.boundaryIncidence,
            outerBoundarySideTie] at hvrow hvcol hs ⊢ <;> omega

theorem contactPair_exact_duplicated_corner
    (previous current : ContactEnrichedCanonicalMergerToken axis hn2 hT)
    (hcontact : previous.contact.1 = current.contact.1)
    (hkey : contactSpatialKey axis hn2 hT previous <
      contactSpatialKey axis hn2 hT current) :
    (axis = .rows ∧
        previous.boundarySide axis hn2 hT = .bottom ∧
        current.boundarySide axis hn2 hT = .left) ∨
      (axis = .columns ∧
        previous.boundarySide axis hn2 hT = .top ∧
        current.boundarySide axis hn2 hT = .right) := by
  have htie : outerBoundarySideTie (previous.boundarySide axis hn2 hT) <
      outerBoundarySideTie (current.boundarySide axis hn2 hT) := by
    unfold contactSpatialKey at hkey
    rw [hcontact] at hkey
    omega
  let p := previous.unsupportedDemand.1
  let q := current.unsupportedDemand.1
  have hv : (CanonicalShoreDemand.boundaryIncidence axis hn2 p).1 =
      (CanonicalShoreDemand.boundaryIncidence axis hn2 q).1 := by
    simpa using hcontact
  have hs : outerBoundarySideTie
        (CanonicalShoreDemand.boundaryIncidence axis hn2 p).2 <
      outerBoundarySideTie
        (CanonicalShoreDemand.boundaryIncidence axis hn2 q).2 := by
    simpa [ContactEnrichedCanonicalMergerToken.boundarySide] using htie
  simpa [ContactEnrichedCanonicalMergerToken.boundarySide] using
    canonicalDemandPair_exact_duplicated_corner axis hn2
      previous.unsupportedDemand.1 current.unsupportedDemand.1 hv hs

theorem duplicatedCornerOverlapDebt_exact
    {component : ContactRawComponent (T := T)}
    (debt : DuplicatedCornerOverlapDebt axis hn2 hT component) :
    (axis = .rows ∧
        debt.1.1.1.contact.1.1.val + 1 = n ∧
        debt.1.1.1.contact.1.2.val = 0 ∧
        (componentSpatialGapPredecessor axis hn2 hT debt.1).1.boundarySide
          axis hn2 hT = .bottom ∧
        debt.1.1.1.boundarySide axis hn2 hT = .left) ∨
      (axis = .columns ∧
        debt.1.1.1.contact.1.1.val = 0 ∧
        debt.1.1.1.contact.1.2.val + 1 = n ∧
        (componentSpatialGapPredecessor axis hn2 hT debt.1).1.boundarySide
          axis hn2 hT = .top ∧
        debt.1.1.1.boundarySide axis hn2 hT = .right) := by
  have hlt := componentSpatialGapPredecessor_rank_lt axis hn2 hT debt.1
  have hp := (componentSpatialGapPredecessor axis hn2 hT debt.1).1.boundarySide_incidence
    axis hn2 hT
  have hc := debt.1.1.1.boundarySide_incidence axis hn2 hT
  have heqrow :
      (componentSpatialGapPredecessor axis hn2 hT debt.1).1.contact.1.1.val =
        debt.1.1.1.contact.1.1.val :=
    congrArg (fun v : GridVertex n n => v.1.val) debt.2
  have heqcol :
      (componentSpatialGapPredecessor axis hn2 hT debt.1).1.contact.1.2.val =
        debt.1.1.1.contact.1.2.val :=
    congrArg (fun v : GridVertex n n => v.2.val) debt.2
  rcases contactPair_exact_duplicated_corner axis hn2 hT
    (componentSpatialGapPredecessor axis hn2 hT debt.1).1 debt.1.1.1
    debt.2 hlt with h | h
  · left
    refine ⟨h.1, ?_, ?_, h.2⟩
    · rw [h.2.1] at hp
      omega
    · rw [h.2.2] at hc
      exact hc
  · right
    refine ⟨h.1, ?_, ?_, h.2⟩
    · rw [h.2.1] at hp
      omega
    · rw [h.2.2] at hc
      omega

theorem duplicatedCornerOverlapDebt_subsingleton
    {component : ContactRawComponent (T := T)}
    (a b : DuplicatedCornerOverlapDebt axis hn2 hT component) : a = b := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply contactSpatialKey_injective axis hn2 hT
  rcases duplicatedCornerOverlapDebt_exact axis hn2 hT a with ha | ha <;>
    rcases duplicatedCornerOverlapDebt_exact axis hn2 hT b with hb | hb
  · unfold contactSpatialKey
    have hc : a.1.1.1.contact.1 = b.1.1.1.contact.1 := by
      apply Prod.ext <;> apply Fin.ext
      · omega
      · exact ha.2.2.1.trans hb.2.2.1.symm
    rw [hc, ha.2.2.2.2, hb.2.2.2.2]
  · simp_all
  · simp_all
  · unfold contactSpatialKey
    have hc : a.1.1.1.contact.1 = b.1.1.1.contact.1 := by
      apply Prod.ext <;> apply Fin.ext
      · exact ha.2.1.trans hb.2.1.symm
      · omega
    rw [hc, ha.2.2.2.2, hb.2.2.2.2]

theorem card_duplicatedCornerOverlapDebt_le_one
    (component : ContactRawComponent (T := T)) :
  Fintype.card (DuplicatedCornerOverlapDebt axis hn2 hT component) ≤ 1 :=
  Fintype.card_le_one_iff.mpr
    (duplicatedCornerOverlapDebt_subsingleton axis hn2 hT)

/-! ### Missing crosscut-to-expanded-contour bridge -/

/-- Strict forward interval in the unique expanded contour cycle. This is an
order statement on occurrences, not merely on their primal base vertices. -/
def OpenExpandedContourInterval
    (start finish x : GridCompassSlot n n) : Prop :=
  x ∈ permOpenForwardInterval (GridExpandedContour.equiv (T := T))
    start finish
    (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
      hn2 hT start finish)

/-- Strong uniform form of corner outer-port separation. It is the exact
topological bridge currently absent from the crosscut APIs: each open contour
interval between the two retained inward corner occurrences contains a marked
outer-port occurrence. -/
structure DuplicatedCornerOpenIntervalsMarked
    {component : ContactRawComponent (T := T)}
    (debt : DuplicatedCornerOverlapDebt axis hn2 hT component) where
  previousSlot : GridCompassSlot n n :=
    GridExpandedContour.slotOfDart
      (componentSpatialGapPredecessor axis hn2 hT debt.1).1.inwardDart
  currentSlot : GridCompassSlot n n :=
    GridExpandedContour.slotOfDart debt.1.1.1.inwardDart
  previousSlot_eq : previousSlot = GridExpandedContour.slotOfDart
    (componentSpatialGapPredecessor axis hn2 hT debt.1).1.inwardDart
  currentSlot_eq : currentSlot =
    GridExpandedContour.slotOfDart debt.1.1.1.inwardDart
  firstMark : ↥(markedSlots (T := T))
  secondMark : ↥(markedSlots (T := T))
  first_open : OpenExpandedContourInterval hn2 hT
    previousSlot currentSlot firstMark.1
  second_open : OpenExpandedContourInterval hn2 hT
    currentSlot previousSlot secondMark.1
  marks_ne : firstMark ≠ secondMark

theorem DuplicatedCornerOpenIntervalsMarked.outerPorts_ne
    {component : ContactRawComponent (T := T)}
    {debt : DuplicatedCornerOverlapDebt axis hn2 hT component}
    (separation : DuplicatedCornerOpenIntervalsMarked axis hn2 hT debt) :
    outerPortOfMarkedSlot (T := T) separation.firstMark ≠
      outerPortOfMarkedSlot (T := T) separation.secondMark := by
  intro h
  exact separation.marks_ne
    (outerPortOfMarkedSlot_injective (T := T) h)

/-- Southwest row-sweep specialization. The side/coordinate conclusion is
already forced by `duplicatedCornerOverlapDebt_exact`; only the uniform
topological separation gate remains. -/
theorem southwest_firstOuterPort_ne
    {component : ContactRawComponent (T := T)}
    (debt : DuplicatedCornerOverlapDebt .rows hn2 hT component)
    (separation : DuplicatedCornerOpenIntervalsMarked .rows hn2 hT debt) :
    outerPortOfMarkedSlot (T := T) separation.firstMark ≠
      outerPortOfMarkedSlot (T := T) separation.secondMark :=
  separation.outerPorts_ne .rows hn2 hT

/-- Northeast column-sweep specialization of the same occurrence-order gate. -/
theorem northeast_firstOuterPort_ne
    {component : ContactRawComponent (T := T)}
    (debt : DuplicatedCornerOverlapDebt .columns hn2 hT component)
    (separation : DuplicatedCornerOpenIntervalsMarked .columns hn2 hT debt) :
    outerPortOfMarkedSlot (T := T) separation.firstMark ≠
      outerPortOfMarkedSlot (T := T) separation.secondMark :=
  separation.outerPorts_ne .columns hn2 hT

/-- A supported boundary vertex supplies a marked expanded slot based at that
vertex. The side incidence is chosen geometrically, including either copy at a
corner. -/
theorem exists_markedSlot_at_supported_boundary
    (v : GridVertex n n)
    (hvSupport : v ∈ supportFinset (gridGraph n n \ T))
    (hvBoundary : IsGridBoundary v) :
    ∃ mark : ↥(markedSlots (T := T)), mark.1.1 = v := by
  rcases hvBoundary with htop | hbottom | hleft | hright
  · let port : GridCotreeOuterPort T :=
      OuterBoundaryPort.ofSupportedVertexSide v hvSupport .top htop
    exact ⟨⟨GridExpandedContour.outerPortSlot port,
      Finset.mem_image.mpr ⟨port, Finset.mem_univ _, rfl⟩⟩, rfl⟩
  · let port : GridCotreeOuterPort T :=
      OuterBoundaryPort.ofSupportedVertexSide v hvSupport .bottom hbottom
    exact ⟨⟨GridExpandedContour.outerPortSlot port,
      Finset.mem_image.mpr ⟨port, Finset.mem_univ _, rfl⟩⟩, rfl⟩
  · let port : GridCotreeOuterPort T :=
      OuterBoundaryPort.ofSupportedVertexSide v hvSupport .left hleft
    exact ⟨⟨GridExpandedContour.outerPortSlot port,
      Finset.mem_image.mpr ⟨port, Finset.mem_univ _, rfl⟩⟩, rfl⟩
  · let port : GridCotreeOuterPort T :=
      OuterBoundaryPort.ofSupportedVertexSide v hvSupport .right hright
    exact ⟨⟨GridExpandedContour.outerPortSlot port,
      Finset.mem_image.mpr ⟨port, Finset.mem_univ _, rfl⟩⟩, rfl⟩

theorem boundary_vertex_preserves_of_no_targetShore_mark
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (d : GridDirectionalDart T)
    (hnoMark : Disjoint (GridExpandedContour.expandedTargetShoreSlots d)
      (markedSlots (T := T)))
    (v : GridVertex n n) (hvShore : v ∈ d.targetShoreVertices)
    (hvBoundary : IsGridBoundary v) :
    preservesIncidentEdges (gridGraph n n) T v := by
  by_contra hnot
  have hvSupport := (mem_supportFinset_sdiff_iff_not_preserves
    (gridGraph n n) T hT.le v).2 hnot
  obtain ⟨mark, hmarkBase⟩ := exists_markedSlot_at_supported_boundary
    (T := T) v hvSupport hvBoundary
  have hshore : mark.1 ∈ GridExpandedContour.expandedTargetShoreSlots d := by
    rw [GridExpandedContour.mem_expandedTargetShoreSlots, hmarkBase]
    exact hvShore
  exact Finset.disjoint_left.mp hnoMark hshore mark.2

/-- Boundary propagation in a fundamental shore. Avoiding the attachment source
ensures that every retained walk edge survives deletion of the attachment. -/
theorem targetShore_end_mem_of_boundary_walk_of_no_mark
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (d : GridDirectionalDart T) {u v : GridVertex n n}
    (walk : (gridGraph n n).Walk u v)
    (huShore : u ∈ d.targetShoreVertices)
    (hboundary : ∀ x ∈ walk.support, IsGridBoundary x)
    (hsourceAvoid : d.source ∉ walk.support)
    (hnoMark : Disjoint (GridExpandedContour.expandedTargetShoreSlots d)
      (markedSlots (T := T))) :
    v ∈ d.targetShoreVertices := by
  induction walk with
  | nil => exact huShore
  | @cons u w v huw rest ih =>
      have huPreserves := boundary_vertex_preserves_of_no_targetShore_mark
        hT d hnoMark u huShore (hboundary u (by simp))
      have hTuw : T.Adj u w := huPreserves huw
      have hedgeNe : s(u, w) ≠ d.edgeSym2 := by
        intro hedge
        rw [GridDirectionalDart.edgeSym2, Sym2.eq_iff] at hedge
        rcases hedge with ⟨hu, hw⟩ | ⟨hu, hw⟩
        · exact hsourceAvoid (by simp [hu])
        · apply hsourceAvoid
          rw [← hw]
          simp
      have hdelete : (T.deleteEdges ({d.edgeSym2} :
          Set (Sym2 (GridVertex n n)))).Adj u w := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hTuw, by simpa using hedgeNe⟩
      have hwShore : w ∈ d.targetShoreVertices := by
        rw [GridDirectionalDart.mem_targetShoreVertices]
        exact (by
          rw [GridDirectionalDart.mem_targetShoreVertices] at huShore
          exact huShore.trans hdelete.reachable)
      apply ih
      · exact hwShore
      · intro x hx
        exact hboundary x (by simp [hx])
      · intro hs
        exact hsourceAvoid (by simp [hs])

/-- Exact corner separation statement, placed after the boundary shore-walk
propagation infrastructure used by its topological proof. -/
def CornerOuterPortSeparationTopologicalLemma : Prop :=
  ∀ (component : ContactRawComponent (T := T))
    (debt : DuplicatedCornerOverlapDebt axis hn2 hT component),
    Nonempty (DuplicatedCornerOpenIntervalsMarked axis hn2 hT debt)

/-
  intro component debt
  let f := GridExpandedContour.equiv (T := T)
  have hf := GridExpandedContour.equiv_isCycle_of_spanningSquareTree hn2 hT
  have cycle_partition (start finish x : GridCompassSlot n n)
      (hstart : f start ≠ start) (hne : start ≠ finish) :
      x = start ∨ x = finish ∨
        x ∈ permOpenForwardInterval f start finish
          (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
            hn2 hT start finish) ∨
        x ∈ permOpenForwardInterval f finish start
          (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
            hn2 hT finish start) := by
    let hsf := GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
      hn2 hT start finish
    let hfs := GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
      hn2 hT finish start
    let d := permForwardDistance f start finish hsf
    let e := permForwardDistance f finish start hfs
    have hdpos : 0 < d := by
      by_contra h
      have hd : d = 0 := Nat.eq_zero_of_not_pos h
      have := permForwardDistance_spec f start finish hsf
      simp [d, hd] at this
      exact hne this
    have hepos : 0 < e := by
      by_contra h
      have he : e = 0 := Nat.eq_zero_of_not_pos h
      have := permForwardDistance_spec f finish start hfs
      simp [e, he] at this
      exact hne this.symm
    have hsum : d + e = orderOf f := by
      have hfix : (f ^ (d + e)) start = start := by
        rw [show d + e = e + d by omega, pow_add, Equiv.Perm.mul_apply,
          permForwardDistance_spec f start finish hsf,
          permForwardDistance_spec f finish start hfs]
      have hpow : f ^ (d + e) = 1 :=
        (hf.pow_eq_one_iff' hstart).2 (by simpa using hfix)
      have hlower : orderOf f ≤ d + e :=
        Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hpow)
      have heupper : e ≤ orderOf f - d := by
        apply Nat.find_min'
        constructor
        · have hdlt := permForwardDistance_lt_orderOf f start finish hsf
          omega
        · have hfinish : finish = (f ^ d) start :=
            (permForwardDistance_spec f start finish hsf).symm
          rw [hfinish, ← Equiv.Perm.mul_apply, ← pow_add]
          rw [show orderOf f - d + d = orderOf f by
            exact Nat.sub_add_cancel
              (Nat.le_of_lt (permForwardDistance_lt_orderOf f start finish hsf))]
          simp
      have hupper : d + e ≤ orderOf f := by
        have hdle := Nat.le_of_lt
          (permForwardDistance_lt_orderOf f start finish hsf)
        omega
      omega
    obtain ⟨k, hklt, hk⟩ :=
      (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
        hn2 hT start x).exists_pow_eq'
    by_cases hkzero : k = 0
    · left
      subst k
      simpa using hk.symm
    by_cases hkd : k < d
    · right; right; left
      rw [mem_permOpenForwardInterval_iff]
      exact ⟨k, Nat.pos_of_ne_zero hkzero, hkd, hk⟩
    by_cases hkdeq : k = d
    · right; left
      subst k
      exact hk.symm.trans (permForwardDistance_spec f start finish hsf)
    right; right; right
    let j := k - d
    have hdlt : d < k := lt_of_le_of_ne (Nat.le_of_not_gt hkd) (Ne.symm hkdeq)
    have hjpos : 0 < j := by omega
    have hjlt : j < e := by
      have hdj : d + j = k := by
        simp [j, Nat.add_sub_of_le (Nat.le_of_lt hdlt)]
      have hklt' : k < orderOf f := by simpa [f] using hklt
      omega
    have hjpow : (f ^ j) finish = x := by
      rw [show finish = (f ^ d) start by
        exact (permForwardDistance_spec f start finish hsf).symm]
      rw [← Equiv.Perm.mul_apply, ← pow_add]
      have hdj : j + d = k := by
        simp [j, Nat.sub_add_cancel (Nat.le_of_lt hdlt)]
      simpa [hdj] using hk
    rw [mem_permOpenForwardInterval_iff]
    exact ⟨j, hjpos, hjlt, hjpow⟩
  have shifted_open_subset (exit entry : GridCompassSlot n n)
      (hne : exit ≠ entry) :
      permOpenForwardInterval f (f exit) entry
          (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
            hn2 hT (f exit) entry) ⊆
        permOpenForwardInterval f exit entry
          (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
            hn2 hT exit entry) := by
    let hnext := GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
      hn2 hT (f exit) entry
    let hexit := GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
      hn2 hT exit entry
    let a := permForwardDistance f (f exit) entry hnext
    let b := permForwardDistance f exit entry hexit
    have hbpos : 0 < b := by
      by_contra h
      have hb : b = 0 := Nat.eq_zero_of_not_pos h
      have := permForwardDistance_spec f exit entry hexit
      simp [b, hb] at this
      exact hne this
    have hba : b = a + 1 := by
      have ha1lt : a + 1 < orderOf f := by
        have halt := permForwardDistance_lt_orderOf f (f exit) entry hnext
        by_contra hnot
        have heq : a + 1 = orderOf f := by omega
        apply hne
        have hspec := permForwardDistance_spec f (f exit) entry hnext
        rw [← Equiv.Perm.mul_apply, ← pow_succ, heq] at hspec
        simpa using hspec
      have hle : b ≤ a + 1 := by
        apply Nat.find_min'
        constructor
        · exact ha1lt
        · rw [pow_succ, Equiv.Perm.mul_apply]
          exact permForwardDistance_spec f (f exit) entry hnext
      have hge : a + 1 ≤ b := by
        by_contra hnot
        have hb_le_a : b ≤ a := by omega
        let k := b - 1
        have hklt : k < a := by omega
        have hkpow : (f ^ k) (f exit) = entry := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ]
          have hkb : k + 1 = b := by simp [k, Nat.sub_add_cancel hbpos]
          simpa [hkb] using permForwardDistance_spec f exit entry hexit
        have ha_le_k : a ≤ k := by
          apply Nat.find_min'
          exact ⟨lt_trans hklt
            (permForwardDistance_lt_orderOf f (f exit) entry hnext), hkpow⟩
        omega
      omega
    intro x hx
    obtain ⟨k, hkpos, hklt, hk⟩ :=
      (mem_permOpenForwardInterval_iff f (f exit) entry x hnext).mp hx
    rw [mem_permOpenForwardInterval_iff]
    refine ⟨k + 1, by omega, ?_, ?_⟩
    · change k + 1 < b
      rw [hba]
      omega
    · rw [pow_succ, Equiv.Perm.mul_apply]
      exact hk
  have opposite_disjoint (d : GridDirectionalDart T)
      (finish : GridCompassSlot n n)
      (hfinish : f (GridExpandedContour.slotOfDart d.reverse) = finish)
      (hne : GridExpandedContour.slotOfDart d.reverse ≠
        GridExpandedContour.slotOfDart d) :
      Disjoint
        (permOpenForwardInterval f finish (GridExpandedContour.slotOfDart d)
          (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
            hn2 hT finish (GridExpandedContour.slotOfDart d)))
        (GridExpandedContour.expandedTargetShoreSlots d) := by
    apply Finset.disjoint_of_subset_left
      (show permOpenForwardInterval f finish (GridExpandedContour.slotOfDart d)
          (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
            hn2 hT finish (GridExpandedContour.slotOfDart d)) ⊆
        permOpenForwardInterval f (GridExpandedContour.slotOfDart d.reverse)
          (GridExpandedContour.slotOfDart d)
          (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT _ _) by
        rw [← hfinish]
        exact shifted_open_subset _ _ hne)
    exact GridExpandedContour.disjoint_permOpenForwardInterval_exit_entry_targetShore
      hn2 hT d
  have slots_ne_of_directions_ne (a b : GridDirectionalDart T)
      (hdir : a.direction ≠ b.direction) :
      GridExpandedContour.slotOfDart a ≠ GridExpandedContour.slotOfDart b := by
    intro h
    exact hdir (congrArg Prod.snd h)
  cases axis with
  | rows =>
    have hsw :
        debt.1.1.1.contact.1.1.val + 1 = n ∧
        debt.1.1.1.contact.1.2.val = 0 ∧
        (componentSpatialGapPredecessor .rows hn2 hT debt.1).1.boundarySide
          .rows hn2 hT = .bottom ∧
        debt.1.1.1.boundarySide .rows hn2 hT = .left := by
      rcases duplicatedCornerOverlapDebt_exact .rows hn2 hT debt with h | h
      · exact h.2
      · exact ShoreSweepAxis.noConfusion h.1
    let previous := (componentSpatialGapPredecessor .rows hn2 hT debt.1).1
    let current := debt.1.1.1
    let dp := previous.inwardDart
    let dc := current.inwardDart
    let ps := GridExpandedContour.slotOfDart dp
    let cs := GridExpandedContour.slotOfDart dc
    have hpSource : dp.source = current.contact.1 := debt.2
    have hcSource : dc.source = current.contact.1 := rfl
    have hpDirection : dp.direction = .north := by
      change (previous.boundarySide .rows hn2 hT).inwardDirection = .north
      rw [hsw.2.2.1]
      rfl
    have hcDirection : dc.direction = .east := by
      change (current.boundarySide .rows hn2 hT).inwardDirection = .east
      rw [hsw.2.2.2]
      rfl
    have hslots : ps ≠ cs := slots_ne_of_directions_ne dp dc (by
      rw [hpDirection, hcDirection]
      decide)
    have hpExitNe : GridExpandedContour.slotOfDart dp.reverse ≠ ps :=
      slots_ne_of_directions_ne dp.reverse dp (by
        change dp.direction.opposite ≠ dp.direction
        rw [hpDirection]
        decide)
    have hcExitNe : GridExpandedContour.slotOfDart dc.reverse ≠ cs :=
      slots_ne_of_directions_ne dc.reverse dc (by
        change dc.direction.opposite ≠ dc.direction
        rw [hcDirection]
        decide)
    have hsuccP : f (GridExpandedContour.slotOfDart dp.reverse) = cs := by
      dsimp [f]
      rw [GridExpandedContour.succ_slotOfDart]
      apply Prod.ext
      · change dp.source = dc.source
        exact hpSource.trans hcSource.symm
      · change dp.direction.opposite.opposite.clockwise = dc.direction
        rw [hpDirection, hcDirection]
        rfl
    have hsuccC : f (GridExpandedContour.slotOfDart dc.reverse) = ps := by
      dsimp [f]
      rw [GridExpandedContour.succ_slotOfDart]
      apply Prod.ext
      · change dc.source = dp.source
        exact hcSource.trans hpSource.symm
      · change dc.direction.opposite.opposite.clockwise = dp.direction
        rw [hpDirection, hcDirection]
        rfl
    have hmoveP : f ps ≠ ps := by
      intro h
      have hv := congrArg Prod.fst h
      dsimp [f] at hv
      rw [GridExpandedContour.succ_slotOfDart] at hv
      exact dp.adj.ne hv.symm
    have hmoveC : f cs ≠ cs := by
      intro h
      have hv := congrArg Prod.fst h
      dsimp [f] at hv
      rw [GridExpandedContour.succ_slotOfDart] at hv
      exact dc.adj.ne hv.symm
    have hcontact : current.contact.1 =
        (⟨n - 1, by omega⟩, ⟨0, by omega⟩) := by
      apply Prod.ext <;> apply Fin.ext
      · change current.contact.1.1.val = n - 1
        have := hsw.1
        omega
      · exact hsw.2.1
    have hpTarget : dp.target =
        (⟨n - 2, by omega⟩, ⟨0, by omega⟩) := by
      have hs := dp.step
      rw [hpSource, hcontact, hpDirection] at hs
      have hneighbor : gridNeighbor?
          ((⟨n - 1, by omega⟩, ⟨0, by omega⟩) : GridVertex n n) .north =
          some ((⟨n - 2, by omega⟩, ⟨0, by omega⟩) : GridVertex n n) := by
        simp [gridNeighbor?, show 0 < n - 1 by omega]
        apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
      rw [hneighbor] at hs
      exact (Option.some.inj hs).symm
    have hcTarget : dc.target =
        (⟨n - 1, by omega⟩, ⟨1, by omega⟩) := by
      have hs := dc.step
      rw [hcSource, hcontact, hcDirection] at hs
      have hneighbor : gridNeighbor?
          ((⟨n - 1, by omega⟩, ⟨0, by omega⟩) : GridVertex n n) .east =
          some ((⟨n - 1, by omega⟩, ⟨1, by omega⟩) : GridVertex n n) := by
        simp [gridNeighbor?, show 1 < n by omega]
      rw [hneighbor] at hs
      exact (Option.some.inj hs).symm
    let start : GridBoundaryPosition n n := ⟨3 * n - 2, by
      unfold gridBoundaryLength
      omega⟩
    let longWalk := gridBoundaryForwardWalk hn2 hn2 start (4 * n - 6)
    have hwalkStart : gridBoundaryVertex hn2 hn2 start = dp.target := by
      rw [hpTarget]
      apply Prod.ext <;> apply Fin.ext
      · rw [gridBoundaryVertex_left hn2 hn2 start (by simp [start]; omega)]
        simp [start, gridBoundaryLength]
        omega
      · rw [gridBoundaryVertex_left hn2 hn2 start (by simp [start]; omega)]
    have hoffset : cyclicOffset (gridBoundaryLength_pos hn2 hn2) start
          (4 * n - 6) = ⟨3 * n - 4, by
            unfold gridBoundaryLength
            omega⟩ := by
      apply Fin.ext
      change (3 * n - 2 + (4 * n - 6)) % gridBoundaryLength n n = 3 * n - 4
      have hsum : 3 * n - 2 + (4 * n - 6) =
          gridBoundaryLength n n + (3 * n - 4) := by
        unfold gridBoundaryLength
        omega
      rw [hsum, Nat.add_mod, Nat.mod_self, zero_add,
        Nat.mod_eq_of_lt]
      unfold gridBoundaryLength
      omega
    have hwalkEnd : gridBoundaryVertex hn2 hn2
          (cyclicOffset (gridBoundaryLength_pos hn2 hn2) start (4 * n - 6)) =
        dc.target := by
      rw [hoffset, hcTarget,
        gridBoundaryVertex_bottom hn2 hn2 ⟨3 * n - 4, by
          unfold gridBoundaryLength
          omega⟩ (by omega) (by omega)]
      apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
    let walk : (gridGraph n n).Walk dp.target dc.target :=
      longWalk.copy hwalkStart hwalkEnd
    have hboundary : ∀ x ∈ walk.support, IsGridBoundary x := by
      intro x hx
      dsimp [walk] at hx
      rw [SimpleGraph.Walk.support_copy,
        mem_support_gridBoundaryForwardWalk_iff] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact gridBoundaryVertex_isBoundary hn2 hn2 _
    have hsourceAvoid : dp.source ∉ walk.support := by
      intro hx
      have hx' := hx
      dsimp [walk] at hx'
      rw [SimpleGraph.Walk.support_copy,
        mem_support_gridBoundaryForwardWalk_iff] at hx'
      obtain ⟨t, ht, hv⟩ := hx'
      have hi := congrArg gridBoundaryIndex hv
      rw [gridBoundaryIndex_vertex] at hi
      have hindexSource : gridBoundaryIndex dp.source = 3 * n - 3 := by
        rw [hpSource, hcontact]
        simp [gridBoundaryIndex]
        omega
      rw [hindexSource] at hi
      change 3 * n - 3 =
        (3 * n - 2 + t) % gridBoundaryLength n n at hi
      by_cases htwrap : t < n - 2
      · rw [Nat.mod_eq_of_lt] at hi
        · omega
        · unfold gridBoundaryLength
          omega
      · have hsum : 3 * n - 2 + t = gridBoundaryLength n n + (t - (n - 2)) := by
          unfold gridBoundaryLength
          omega
        rw [hsum, Nat.add_mod, Nat.mod_self, zero_add,
          Nat.mod_eq_of_lt] at hi
        · omega
        · unfold gridBoundaryLength
          omega
    have hmarkFirst : ∃ mark : ↥(markedSlots (T := T)),
        OpenExpandedContourInterval hn2 hT ps cs mark.1 := by
      by_contra hnone
      push_neg at hnone
      have hno : Disjoint (GridExpandedContour.expandedTargetShoreSlots dp)
          (markedSlots (T := T)) := by
        rw [Finset.disjoint_left]
        intro slot hshore hmark
        rcases cycle_partition ps cs slot hmoveP hslots with
          rfl | rfl | hopen | hopen
        · rw [GridExpandedContour.mem_expandedTargetShoreSlots] at hshore
          exact dp.source_notMem_targetShoreVertices hT.isAcyclic hshore
        · rw [GridExpandedContour.mem_expandedTargetShoreSlots] at hshore
          change dc.source ∈ dp.targetShoreVertices at hshore
          apply dp.source_notMem_targetShoreVertices hT.isAcyclic
          exact hpSource.trans hcSource.symm ▸ hshore
        · exact hnone ⟨slot, hmark⟩ (by simpa [OpenExpandedContourInterval] using hopen)
        · exact Finset.disjoint_left.mp (opposite_disjoint dp cs hsuccP hpExitNe)
            hopen hshore
      have hend := targetShore_end_mem_of_boundary_walk_of_no_mark hT dp walk
        dp.target_mem_targetShoreVertices hboundary hsourceAvoid hno
      have hedge := GridDirectionalDart.edgeSym2_eq_of_source_mem_target_notMem
        dp dc.reverse (by simpa [GridDirectionalDart.reverse] using hend)
        (by
          simpa [GridDirectionalDart.reverse, hpSource, hcSource] using
            dp.source_notMem_targetShoreVertices hT.isAcyclic)
      rw [GridDirectionalDart.edgeSym2, GridDirectionalDart.edgeSym2,
        GridDirectionalDart.reverse, Sym2.eq_iff] at hedge
      rcases hedge with h | h
      · exact dp.adj.ne h.1
      · exact dc.adj.ne h.2.symm
    have hmarkSecond : ∃ mark : ↥(markedSlots (T := T)),
        OpenExpandedContourInterval hn2 hT cs ps mark.1 := by
      by_contra hnone
      push_neg at hnone
      have hno : Disjoint (GridExpandedContour.expandedTargetShoreSlots dc)
          (markedSlots (T := T)) := by
        rw [Finset.disjoint_left]
        intro slot hshore hmark
        rcases cycle_partition cs ps slot hmoveC hslots.symm with
          rfl | rfl | hopen | hopen
        · rw [GridExpandedContour.mem_expandedTargetShoreSlots] at hshore
          exact dc.source_notMem_targetShoreVertices hT.isAcyclic hshore
        · rw [GridExpandedContour.mem_expandedTargetShoreSlots] at hshore
          change dp.source ∈ dc.targetShoreVertices at hshore
          apply dc.source_notMem_targetShoreVertices hT.isAcyclic
          exact hcSource.trans hpSource.symm ▸ hshore
        · exact hnone ⟨slot, hmark⟩ (by simpa [OpenExpandedContourInterval] using hopen)
        · exact Finset.disjoint_left.mp (opposite_disjoint dc ps hsuccC hcExitNe)
            hopen hshore
      have hsourceAvoid' : dc.source ∉ walk.reverse.support := by
        simpa [SimpleGraph.Walk.support_reverse, hpSource, hcSource] using hsourceAvoid
      have hboundary' : ∀ x ∈ walk.reverse.support, IsGridBoundary x := by
        intro x hx
        apply hboundary x
        simpa [SimpleGraph.Walk.support_reverse] using hx
      have hend := targetShore_end_mem_of_boundary_walk_of_no_mark hT dc walk.reverse
        dc.target_mem_targetShoreVertices hboundary' hsourceAvoid' hno
      have hedge := GridDirectionalDart.edgeSym2_eq_of_source_mem_target_notMem
        dc dp.reverse (by simpa [GridDirectionalDart.reverse] using hend)
        (by
          simpa [GridDirectionalDart.reverse, hpSource, hcSource] using
            dc.source_notMem_targetShoreVertices hT.isAcyclic)
      rw [GridDirectionalDart.edgeSym2, GridDirectionalDart.edgeSym2,
        GridDirectionalDart.reverse, Sym2.eq_iff] at hedge
      rcases hedge with h | h
      · exact dc.adj.ne h.1
      · exact dp.adj.ne h.2.symm
    obtain ⟨firstMark, hfirst⟩ := hmarkFirst
    obtain ⟨secondMark, hsecond⟩ := hmarkSecond
    refine ⟨{
      previousSlot := ps
      currentSlot := cs
      previousSlot_eq := rfl
      currentSlot_eq := rfl
      firstMark := firstMark
      secondMark := secondMark
      first_open := hfirst
      second_open := hsecond
      marks_ne := ?_ }⟩
    intro heq
    have hval := congrArg Subtype.val heq
    exact hslots (by
      apply forwardCycleRank_injective f ps
        (fun x => GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
          hn2 hT ps x)
      have hfRank := forwardCycleRank_spec f ps
        (fun x => GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
          hn2 hT ps x)
      have hfirst' := hfirst
      have hsecond' := hsecond
      rw [hval] at hfirst'
      simp only [OpenExpandedContourInterval,
        mem_permOpenForwardInterval_iff] at hfirst' hsecond'
      obtain ⟨a, ha0, halt, ha⟩ := hfirst'
      obtain ⟨b, hb0, hblt, hb⟩ := hsecond'
      have hcycle : (f ^ (a + b)) ps = ps := by
        rw [show a + b = b + a by omega, pow_add, Equiv.Perm.mul_apply, ha, hb]
      have hpow : f ^ (a + b) = 1 :=
        (hf.pow_eq_one_iff' hmoveP).2 (by simpa using hcycle)
      have hlower : orderOf f ≤ a + b := Nat.le_of_dvd (by omega)
        (orderOf_dvd_of_pow_eq_one hpow)
      have hablt : a + b < orderOf f := by
        have hsum := show
          permForwardDistance f ps cs
              (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT ps cs) +
            permForwardDistance f cs ps
              (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT cs ps) =
            orderOf f by
          exact hsum
        omega
      omega)
  | columns =>
    -- The original sketch stopped before the column case.
-/

/-- Advancing the finish by one successor advances its forward distance by one,
provided the new finish does not wrap back to the start. -/
private theorem permForwardDistance_succ_right
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish : α)
    (hsame : f.SameCycle start finish)
    (hne : start ≠ f finish) :
    permForwardDistance f start (f finish) hsame.apply_right =
      permForwardDistance f start finish hsame + 1 := by
  let d := permForwardDistance f start finish hsame
  let hnext := hsame.apply_right
  let e := permForwardDistance f start (f finish) hnext
  have hepos : 0 < e := by
    by_contra h
    have he : e = 0 := Nat.eq_zero_of_not_pos h
    have hspec := permForwardDistance_spec f start (f finish) hnext
    simp [e, he] at hspec
    exact hne hspec
  have he_le : e ≤ d + 1 := by
    apply Nat.find_min'
    constructor
    · have hdlt := permForwardDistance_lt_orderOf f start finish hsame
      by_contra hnot
      have heq : d + 1 = orderOf f := by omega
      apply hne
      rw [show f finish = (f ^ (d + 1)) start by
        rw [pow_succ', Equiv.Perm.mul_apply,
          permForwardDistance_spec f start finish hsame]]
      simp [heq]
    · rw [pow_succ', Equiv.Perm.mul_apply,
        permForwardDistance_spec f start finish hsame]
  have hd_lt_e : d < e := by
    by_contra hnot
    let j := e - 1
    have hjpow : (f ^ j) start = finish := by
      apply f.injective
      rw [← Equiv.Perm.mul_apply, ← pow_succ']
      have hje : j + 1 = e := Nat.sub_add_cancel hepos
      simpa [hje] using permForwardDistance_spec f start (f finish) hnext
    have hdle : d ≤ j := by
      apply Nat.find_min'
      exact ⟨lt_of_le_of_lt (Nat.sub_le e 1)
        (permForwardDistance_lt_orderOf f start (f finish) hnext), hjpow⟩
    omega
  omega

/-- A closed segment ending at `finish` lies in the open segment ending one
successor later. -/
private theorem permClosedForwardInterval_subset_open_succ
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish : α)
    (hsame : f.SameCycle start finish)
    (hne : start ≠ f finish) :
    permClosedForwardInterval f start finish hsame ⊆
      permOpenForwardInterval f start (f finish)
        hsame.apply_right := by
  intro x hx
  obtain ⟨k, hkpos, hkle, hk⟩ :=
    (mem_permClosedForwardInterval_iff f start finish x hsame).mp hx
  rw [mem_permOpenForwardInterval_iff,
    permForwardDistance_succ_right f start finish hsame hne]
  exact ⟨k, hkpos, by omega, hk⟩

/-- Extending an open segment by one successor preserves all its members. -/
private theorem permOpenForwardInterval_subset_open_succ
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (start finish : α)
    (hsame : f.SameCycle start finish)
    (hne : start ≠ f finish) :
    permOpenForwardInterval f start finish hsame ⊆
      permOpenForwardInterval f start (f finish)
        hsame.apply_right := by
  intro x hx
  obtain ⟨k, hkpos, hklt, hk⟩ :=
    (mem_permOpenForwardInterval_iff f start finish x hsame).mp hx
  rw [mem_permOpenForwardInterval_iff,
    permForwardDistance_succ_right f start finish hsame hne]
  exact ⟨k, hkpos, by omega, hk⟩

/-- Oppositely oriented open intervals in a nontrivial permutation cycle are
disjoint. -/
private theorem disjoint_permOpenForwardIntervals
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (hf : f.IsCycle) (start finish : α)
    (hmove : f start ≠ start) (hne : start ≠ finish)
    (hsf : f.SameCycle start finish) :
    Disjoint (permOpenForwardInterval f start finish hsf)
      (permOpenForwardInterval f finish start hsf.symm) := by
  rw [Finset.disjoint_left]
  intro x hx hxr
  obtain ⟨a, ha0, halt, ha⟩ :=
    (mem_permOpenForwardInterval_iff f start finish x hsf).mp hx
  obtain ⟨b, hb0, hblt, hb⟩ :=
    (mem_permOpenForwardInterval_iff f finish start x hsf.symm).mp hxr
  let d := permForwardDistance f start finish hsf
  let e := permForwardDistance f finish start hsf.symm
  have hfinish : (f ^ d) start = finish :=
    permForwardDistance_spec f start finish hsf
  have heq : (f ^ a) start = (f ^ (d + b)) start := by
    rw [ha, show d + b = b + d by omega, pow_add,
      Equiv.Perm.mul_apply, hfinish, hb]
  have hpow : f ^ ((d + b) - a) = 1 := by
    apply (hf.pow_eq_one_iff' hmove).2
    rw [show d + b = (d + b - a) + a by omega, pow_add,
      Equiv.Perm.mul_apply] at heq
    apply (f ^ a).injective
    simpa [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm] using heq.symm
  have hlower : orderOf f ≤ (d + b) - a :=
    Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hpow)
  have hsum := permForwardDistance_add_reverse_eq_orderOf f start finish
    hsf hsf.symm hf hmove hne
  omega

/-- The duplicated southwest or northeast corner has a marked outer-port slot
in each complementary open expanded-contour interval. -/
theorem cornerOuterPortSeparationTopologicalLemma :
    CornerOuterPortSeparationTopologicalLemma axis hn2 hT := by
  intro component debt
  let f := GridExpandedContour.equiv (T := T)
  have hf := GridExpandedContour.equiv_isCycle_of_spanningSquareTree hn2 hT
  have mark_of_shore_interval
      (d e : GridDirectionalDart T) (start finish : GridCompassSlot n n)
      (hshore : GridExpandedContour.expandedTargetShoreSlots d ⊆
        permOpenForwardInterval f start finish
          (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree
            hn2 hT start finish))
      (walk : (gridGraph n n).Walk d.target e.target)
      (hboundary : ∀ x ∈ walk.support, IsGridBoundary x)
      (hsourceAvoid : d.source ∉ walk.support)
      (hsources : d.source = e.source)
      (hdirections : d.direction ≠ e.direction) :
      ∃ mark : ↥(markedSlots (T := T)),
        OpenExpandedContourInterval hn2 hT start finish mark.1 := by
    by_contra hnone
    push_neg at hnone
    have hno : Disjoint (GridExpandedContour.expandedTargetShoreSlots d)
        (markedSlots (T := T)) := by
      rw [Finset.disjoint_left]
      intro slot hslot hmark
      exact hnone ⟨slot, hmark⟩ (by
        simpa [OpenExpandedContourInterval] using hshore hslot)
    have hend := targetShore_end_mem_of_boundary_walk_of_no_mark hT d walk
      d.target_mem_targetShoreVertices hboundary hsourceAvoid hno
    have hedge := GridDirectionalDart.edgeSym2_eq_of_source_mem_target_notMem
      d e.reverse (by simpa [GridDirectionalDart.reverse] using hend)
      (by
        simpa [GridDirectionalDart.reverse, hsources] using
          d.source_notMem_targetShoreVertices hT.isAcyclic)
    rw [GridDirectionalDart.edgeSym2, GridDirectionalDart.edgeSym2,
      GridDirectionalDart.reverse, Sym2.eq_iff] at hedge
    rcases hedge with h | h
    · exact d.adj.ne (hsources.trans h.2)
    · apply hdirections
      exact congrArg GridDirectionalDart.direction
        (GridDirectionalDart.ext_endpoints h.2.symm h.1.symm)
  have slots_ne_of_directions_ne (a b : GridDirectionalDart T)
      (hdir : a.direction ≠ b.direction) :
      GridExpandedContour.slotOfDart a ≠ GridExpandedContour.slotOfDart b := by
    intro h
    exact hdir (congrArg Prod.snd h)
  cases axis with
  | rows =>
      have hsw :
          debt.1.1.1.contact.1.1.val + 1 = n ∧
          debt.1.1.1.contact.1.2.val = 0 ∧
          (componentSpatialGapPredecessor .rows hn2 hT debt.1).1.boundarySide
            .rows hn2 hT = .bottom ∧
          debt.1.1.1.boundarySide .rows hn2 hT = .left := by
        rcases duplicatedCornerOverlapDebt_exact .rows hn2 hT debt with h | h
        · exact h.2
        · exact ShoreSweepAxis.noConfusion h.1
      let previous := (componentSpatialGapPredecessor .rows hn2 hT debt.1).1
      let current := debt.1.1.1
      let dp := previous.inwardDart
      let dc := current.inwardDart
      let ps := GridExpandedContour.slotOfDart dp
      let cs := GridExpandedContour.slotOfDart dc
      have hpSource : dp.source = current.contact.1 := debt.2
      have hcSource : dc.source = current.contact.1 := rfl
      have hsources : dp.source = dc.source := hpSource.trans hcSource.symm
      have hpDirection : dp.direction = .north := by
        change (previous.boundarySide .rows hn2 hT).inwardDirection = .north
        rw [hsw.2.2.1]
        rfl
      have hcDirection : dc.direction = .east := by
        change (current.boundarySide .rows hn2 hT).inwardDirection = .east
        rw [hsw.2.2.2]
        rfl
      have hdirections : dp.direction ≠ dc.direction := by
        rw [hpDirection, hcDirection]
        decide
      have hslots : ps ≠ cs := slots_ne_of_directions_ne dp dc hdirections
      have hcontact : current.contact.1 =
          (⟨n - 1, by omega⟩, ⟨0, by omega⟩) := by
        apply Prod.ext <;> apply Fin.ext
        · change current.contact.1.1.val = n - 1
          have hnpos : 0 < n := by omega
          exact Nat.eq_sub_of_add_eq hsw.1
        · exact hsw.2.1
      have hpTarget : dp.target =
          (⟨n - 2, by omega⟩, ⟨0, by omega⟩) := by
        have hs := dp.step
        rw [hpSource, hcontact, hpDirection] at hs
        have hneighbor : gridNeighbor?
            ((⟨n - 1, by omega⟩, ⟨0, by omega⟩) : GridVertex n n) .north =
            some ((⟨n - 2, by omega⟩, ⟨0, by omega⟩) : GridVertex n n) := by
          simp [gridNeighbor?, show 0 < n - 1 by omega]
          apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
        rw [hneighbor] at hs
        exact (Option.some.inj hs).symm
      have hcTarget : dc.target =
          (⟨n - 1, by omega⟩, ⟨1, by omega⟩) := by
        have hs := dc.step
        rw [hcSource, hcontact, hcDirection] at hs
        have hneighbor : gridNeighbor?
            ((⟨n - 1, by omega⟩, ⟨0, by omega⟩) : GridVertex n n) .east =
            some ((⟨n - 1, by omega⟩, ⟨1, by omega⟩) : GridVertex n n) := by
          simp [gridNeighbor?, show 1 < n by omega]
        rw [hneighbor] at hs
        exact (Option.some.inj hs).symm
      have hsuccP : f (GridExpandedContour.slotOfDart dp.reverse) = cs := by
        dsimp [f]
        rw [GridExpandedContour.southwest_succ_north_reverse hn2 dp
          (hsources.trans (hcSource.trans hcontact)) hpDirection]
        apply Prod.ext
        · exact (hcSource.trans hcontact).symm
        · exact hcDirection.symm
      have hsuccC1 : f (GridExpandedContour.slotOfDart dc.reverse) =
          ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .south) := by
        exact GridExpandedContour.southwest_succ_east_reverse hn2 dc
          (hcSource.trans hcontact) hcDirection
      have hsuccC2 : f (f (GridExpandedContour.slotOfDart dc.reverse)) =
          ((⟨n - 1, by omega⟩, ⟨0, by omega⟩), .west) := by
        dsimp [f] at hsuccC1 ⊢
        rw [hsuccC1, GridExpandedContour.southwest_succ_south hn2]
      have hsuccC3 : f (f (f (GridExpandedContour.slotOfDart dc.reverse))) = ps := by
        dsimp [f] at hsuccC2 ⊢
        rw [hsuccC2, GridExpandedContour.southwest_succ_west hn2]
        apply Prod.ext
        · exact (hpSource.trans hcontact).symm
        · exact hpDirection.symm
      have hfirstShore : GridExpandedContour.expandedTargetShoreSlots dp ⊆
          permOpenForwardInterval f ps cs
            (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT ps cs) := by
        rw [GridExpandedContour.expandedTargetShoreSlots_eq_closedForwardInterval
          hn2 hT dp, ← hsuccP]
        exact permClosedForwardInterval_subset_open_succ f ps
          (GridExpandedContour.slotOfDart dp.reverse) _ (by simpa [hsuccP])
      have hsecondShore : GridExpandedContour.expandedTargetShoreSlots dc ⊆
          permOpenForwardInterval f cs ps
            (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT cs ps) := by
        rw [GridExpandedContour.expandedTargetShoreSlots_eq_closedForwardInterval
          hn2 hT dc, ← hsuccC3]
        have hne1 : cs ≠ f (GridExpandedContour.slotOfDart dc.reverse) := by
          intro h
          have hdir := congrArg Prod.snd h
          rw [hsuccC1] at hdir
          change dc.direction = .south at hdir
          rw [hcDirection] at hdir
          exact GridDirection.noConfusion hdir
        have hne2 : cs ≠ f (f (GridExpandedContour.slotOfDart dc.reverse)) := by
          intro h
          have hdir := congrArg Prod.snd h
          rw [hsuccC2] at hdir
          change dc.direction = .west at hdir
          rw [hcDirection] at hdir
          exact GridDirection.noConfusion hdir
        exact (permClosedForwardInterval_subset_open_succ f cs
          (GridExpandedContour.slotOfDart dc.reverse) _ hne1).trans
          ((permOpenForwardInterval_subset_open_succ f cs
            (f (GridExpandedContour.slotOfDart dc.reverse)) _ hne2).trans
            (permOpenForwardInterval_subset_open_succ f cs
              (f (f (GridExpandedContour.slotOfDart dc.reverse))) _ (by
                rw [hsuccC3]
                exact hslots.symm)))
      let walk : (gridGraph n n).Walk dp.target dc.target :=
        (southwestLongBoundaryWalk hn2).copy hpTarget.symm hcTarget.symm
      have hboundary : ∀ x ∈ walk.support, IsGridBoundary x := by
        intro x hx
        exact southwestLongBoundaryWalk_on_boundary hn2 (by simpa [walk] using hx)
      have hsourceAvoid : dp.source ∉ walk.support := by
        simpa [walk] using southwestDartSource_not_mem_longBoundaryWalk hn2 dp
          (hpSource.trans hcontact)
      obtain ⟨firstMark, hfirst⟩ := mark_of_shore_interval dp dc ps cs
        hfirstShore walk hboundary hsourceAvoid hsources hdirections
      have hsourceAvoid' : dc.source ∉ walk.reverse.support := by
        simpa [SimpleGraph.Walk.support_reverse, hsources] using hsourceAvoid
      have hboundary' : ∀ x ∈ walk.reverse.support, IsGridBoundary x := by
        intro x hx
        exact hboundary x (by simpa [SimpleGraph.Walk.support_reverse] using hx)
      obtain ⟨secondMark, hsecond⟩ := mark_of_shore_interval dc dp cs ps
        hsecondShore walk.reverse hboundary' hsourceAvoid' hsources.symm
          (Ne.symm hdirections)
      refine ⟨{
        previousSlot := ps
        currentSlot := cs
        previousSlot_eq := rfl
        currentSlot_eq := rfl
        firstMark := firstMark
        secondMark := secondMark
        first_open := hfirst
        second_open := hsecond
        marks_ne := ?_ }⟩
      intro heq
      exact Finset.disjoint_left.mp
        (disjoint_permOpenForwardIntervals f hf ps cs (by
          intro h
          have hv := congrArg Prod.fst h
          dsimp [f, ps] at hv
          rw [GridExpandedContour.succ_slotOfDart] at hv
          exact dp.adj.ne hv.symm) hslots _)
        hfirst (heq ▸ hsecond)
  | columns =>
      have hne :
          debt.1.1.1.contact.1.1.val = 0 ∧
          debt.1.1.1.contact.1.2.val + 1 = n ∧
          (componentSpatialGapPredecessor .columns hn2 hT debt.1).1.boundarySide
            .columns hn2 hT = .top ∧
          debt.1.1.1.boundarySide .columns hn2 hT = .right := by
        rcases duplicatedCornerOverlapDebt_exact .columns hn2 hT debt with h | h
        · exact ShoreSweepAxis.noConfusion h.1
        · exact h.2
      let previous := (componentSpatialGapPredecessor .columns hn2 hT debt.1).1
      let current := debt.1.1.1
      let dp := previous.inwardDart
      let dc := current.inwardDart
      let ps := GridExpandedContour.slotOfDart dp
      let cs := GridExpandedContour.slotOfDart dc
      have hpSource : dp.source = current.contact.1 := debt.2
      have hcSource : dc.source = current.contact.1 := rfl
      have hsources : dp.source = dc.source := hpSource.trans hcSource.symm
      have hpDirection : dp.direction = .south := by
        change (previous.boundarySide .columns hn2 hT).inwardDirection = .south
        rw [hne.2.2.1]
        rfl
      have hcDirection : dc.direction = .west := by
        change (current.boundarySide .columns hn2 hT).inwardDirection = .west
        rw [hne.2.2.2]
        rfl
      have hdirections : dp.direction ≠ dc.direction := by
        rw [hpDirection, hcDirection]
        decide
      have hslots : ps ≠ cs := slots_ne_of_directions_ne dp dc hdirections
      have hcontact : current.contact.1 =
          (⟨0, by omega⟩, ⟨n - 1, by omega⟩) := by
        apply Prod.ext <;> apply Fin.ext
        · exact hne.1
        · change current.contact.1.2.val = n - 1
          exact Nat.eq_sub_of_add_eq hne.2.1
      have hpTarget : dp.target =
          (⟨1, by omega⟩, ⟨n - 1, by omega⟩) := by
        have hs := dp.step
        rw [hpSource, hcontact, hpDirection] at hs
        have hneighbor : gridNeighbor?
            ((⟨0, by omega⟩, ⟨n - 1, by omega⟩) : GridVertex n n) .south =
            some ((⟨1, by omega⟩, ⟨n - 1, by omega⟩) : GridVertex n n) := by
          simp [gridNeighbor?, show 1 < n by omega]
        rw [hneighbor] at hs
        exact (Option.some.inj hs).symm
      have hcTarget : dc.target =
          (⟨0, by omega⟩, ⟨n - 2, by omega⟩) := by
        have hs := dc.step
        rw [hcSource, hcontact, hcDirection] at hs
        have hneighbor : gridNeighbor?
            ((⟨0, by omega⟩, ⟨n - 1, by omega⟩) : GridVertex n n) .west =
            some ((⟨0, by omega⟩, ⟨n - 2, by omega⟩) : GridVertex n n) := by
          simp [gridNeighbor?, show 0 < n - 1 by omega]
          apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
        rw [hneighbor] at hs
        exact (Option.some.inj hs).symm
      have hsuccP : f (GridExpandedContour.slotOfDart dp.reverse) = cs := by
        dsimp [f]
        rw [GridExpandedContour.northeast_succ_south_reverse hn2 dp
          (hsources.trans (hcSource.trans hcontact)) hpDirection]
        apply Prod.ext
        · exact (hcSource.trans hcontact).symm
        · exact hcDirection.symm
      have hsuccC1 : f (GridExpandedContour.slotOfDart dc.reverse) =
          ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .north) := by
        exact GridExpandedContour.northeast_succ_west_reverse hn2 dc
          (hcSource.trans hcontact) hcDirection
      have hsuccC2 : f (f (GridExpandedContour.slotOfDart dc.reverse)) =
          ((⟨0, by omega⟩, ⟨n - 1, by omega⟩), .east) := by
        dsimp [f] at hsuccC1 ⊢
        rw [hsuccC1, GridExpandedContour.northeast_succ_north hn2]
      have hsuccC3 : f (f (f (GridExpandedContour.slotOfDart dc.reverse))) = ps := by
        dsimp [f] at hsuccC2 ⊢
        rw [hsuccC2, GridExpandedContour.northeast_succ_east hn2]
        apply Prod.ext
        · exact (hpSource.trans hcontact).symm
        · exact hpDirection.symm
      have hfirstShore : GridExpandedContour.expandedTargetShoreSlots dp ⊆
          permOpenForwardInterval f ps cs
            (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT ps cs) := by
        rw [GridExpandedContour.expandedTargetShoreSlots_eq_closedForwardInterval
          hn2 hT dp, ← hsuccP]
        exact permClosedForwardInterval_subset_open_succ f ps
          (GridExpandedContour.slotOfDart dp.reverse) _ (by simpa [hsuccP])
      have hsecondShore : GridExpandedContour.expandedTargetShoreSlots dc ⊆
          permOpenForwardInterval f cs ps
            (GridExpandedContour.equiv_sameCycle_of_spanningSquareTree hn2 hT cs ps) := by
        rw [GridExpandedContour.expandedTargetShoreSlots_eq_closedForwardInterval
          hn2 hT dc, ← hsuccC3]
        have hne1 : cs ≠ f (GridExpandedContour.slotOfDart dc.reverse) := by
          intro h
          have hdir := congrArg Prod.snd h
          rw [hsuccC1] at hdir
          change dc.direction = .north at hdir
          rw [hcDirection] at hdir
          exact GridDirection.noConfusion hdir
        have hne2 : cs ≠ f (f (GridExpandedContour.slotOfDart dc.reverse)) := by
          intro h
          have hdir := congrArg Prod.snd h
          rw [hsuccC2] at hdir
          change dc.direction = .east at hdir
          rw [hcDirection] at hdir
          exact GridDirection.noConfusion hdir
        exact (permClosedForwardInterval_subset_open_succ f cs
          (GridExpandedContour.slotOfDart dc.reverse) _ hne1).trans
          ((permOpenForwardInterval_subset_open_succ f cs
            (f (GridExpandedContour.slotOfDart dc.reverse)) _ hne2).trans
            (permOpenForwardInterval_subset_open_succ f cs
              (f (f (GridExpandedContour.slotOfDart dc.reverse))) _ (by
                rw [hsuccC3]
                exact hslots.symm)))
      let walk : (gridGraph n n).Walk dp.target dc.target :=
        (northeastLongBoundaryWalk hn2).copy hpTarget.symm hcTarget.symm
      have hboundary : ∀ x ∈ walk.support, IsGridBoundary x := by
        intro x hx
        exact northeastLongBoundaryWalk_on_boundary hn2 (by simpa [walk] using hx)
      have hsourceAvoid : dp.source ∉ walk.support := by
        simpa [walk] using northeastDartSource_not_mem_longBoundaryWalk hn2 dp
          (hpSource.trans hcontact)
      obtain ⟨firstMark, hfirst⟩ := mark_of_shore_interval dp dc ps cs
        hfirstShore walk hboundary hsourceAvoid hsources hdirections
      have hsourceAvoid' : dc.source ∉ walk.reverse.support := by
        simpa [SimpleGraph.Walk.support_reverse, hsources] using hsourceAvoid
      have hboundary' : ∀ x ∈ walk.reverse.support, IsGridBoundary x := by
        intro x hx
        exact hboundary x (by simpa [SimpleGraph.Walk.support_reverse] using hx)
      obtain ⟨secondMark, hsecond⟩ := mark_of_shore_interval dc dp cs ps
        hsecondShore walk.reverse hboundary' hsourceAvoid' hsources.symm
          (Ne.symm hdirections)
      refine ⟨{
        previousSlot := ps
        currentSlot := cs
        previousSlot_eq := rfl
        currentSlot_eq := rfl
        firstMark := firstMark
        secondMark := secondMark
        first_open := hfirst
        second_open := hsecond
        marks_ne := ?_ }⟩
      intro heq
      exact Finset.disjoint_left.mp
        (disjoint_permOpenForwardIntervals f hf ps cs (by
          intro h
          have hv := congrArg Prod.fst h
          dsimp [f, ps] at hv
          rw [GridExpandedContour.succ_slotOfDart] at hv
          exact dp.adj.ne hv.symm) hslots _)
        hfirst (heq ▸ hsecond)

/-- Noncoincident component-local gaps. -/
abbrev OrdinaryComponentSpatialGap
    (component : ContactRawComponent (T := T)) :=
  {gap : ComponentSpatialGap axis hn2 hT component //
    (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1 ≠
      gap.1.1.contact.1}

/-- The two contacts of a component-local spatial gap lie in one straight raw
full component. -/
theorem componentSpatialGap_contacts_same_row_or_column
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component) :
    (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.1 =
        gap.1.1.contact.1.1 ∨
      (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.2 =
        gap.1.1.contact.1.2 := by
  let previous := componentSpatialGapPredecessor axis hn2 hT gap
  let current := gap.1
  have hp : previous.1.contact ∈ component.supp := by
    simpa only [previous.2] using previous.1.contact_mem_component axis hn2 hT
  have hc : current.1.contact ∈ component.supp := by
    simpa only [current.2] using current.1.contact_mem_component axis hn2 hT
  rcases cotree_full_component_straight hT component with ⟨row, hrow⟩ | ⟨col, hcol⟩
  · exact Or.inl ((hrow _ hp).trans (hrow _ hc).symm)
  · exact Or.inr ((hcol _ hp).trans (hcol _ hc).symm)

/-- Horizontal interval closure inside a component-local spatial gap. -/
theorem componentSpatialGap_horizontal_intermediate_mem
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component)
    (hrow : (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.1 =
      gap.1.1.contact.1.1)
    (column : Fin n)
    (hbetween :
      ((componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.2.val ≤
          column.val ∧ column.val ≤ gap.1.1.contact.1.2.val) ∨
      (gap.1.1.contact.1.2.val ≤ column.val ∧ column.val ≤
        (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.2.val)) :
    ∃ contact : ↥(↑((Finset.univ : Finset (GridVertex n n)) \
        supportFinset (gridGraph n n \ T)) : Set (GridVertex n n)),
      contact.1 =
          ((componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.1, column) ∧
        contact ∈ component.supp := by
  let previous := componentSpatialGapPredecessor axis hn2 hT gap
  let current := gap.1
  have hp : previous.1.contact ∈ component.supp := by
    simpa only [previous.2] using previous.1.contact_mem_component axis hn2 hT
  have hc : current.1.contact ∈ component.supp := by
    simpa only [current.2] using current.1.contact_mem_component axis hn2 hT
  obtain ⟨hfree, hmem⟩ := induced_forced_connectedComponent_horizontal_interval
    (grid_tree_complement_forcedEdgeGraph_isAcyclic hT) component hp hc hrow
      column hbetween
  exact ⟨⟨_, hfree⟩, rfl, hmem⟩

/-- Vertical interval closure inside a component-local spatial gap. -/
theorem componentSpatialGap_vertical_intermediate_mem
    {component : ContactRawComponent (T := T)}
    (gap : ComponentSpatialGap axis hn2 hT component)
    (hcol : (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.2 =
      gap.1.1.contact.1.2)
    (row : Fin n)
    (hbetween :
      ((componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.1.val ≤
          row.val ∧ row.val ≤ gap.1.1.contact.1.1.val) ∨
      (gap.1.1.contact.1.1.val ≤ row.val ∧ row.val ≤
        (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.1.val)) :
    ∃ contact : ↥(↑((Finset.univ : Finset (GridVertex n n)) \
        supportFinset (gridGraph n n \ T)) : Set (GridVertex n n)),
      contact.1 =
          (row, (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1.2) ∧
        contact ∈ component.supp := by
  let previous := componentSpatialGapPredecessor axis hn2 hT gap
  let current := gap.1
  have hp : previous.1.contact ∈ component.supp := by
    simpa only [previous.2] using previous.1.contact_mem_component axis hn2 hT
  have hc : current.1.contact ∈ component.supp := by
    simpa only [current.2] using current.1.contact_mem_component axis hn2 hT
  obtain ⟨hfree, hmem⟩ := induced_forced_connectedComponent_vertical_interval
    (grid_tree_complement_forcedEdgeGraph_isAcyclic hT) component hp hc hcol
      row hbetween
  exact ⟨⟨_, hfree⟩, rfl, hmem⟩

private theorem min_add_one_lt_of_lt_of_ne {a b n : Nat}
    (ha : a < n) (hb : b < n) (hne : a ≠ b) : min a b + 1 < n := by
  omega

private theorem min_between {a b : Nat} :
    (a ≤ min a b ∧ min a b ≤ b) ∨ (b ≤ min a b ∧ min a b ≤ a) := by
  omega

private theorem min_add_one_between {a b : Nat} (hne : a ≠ b) :
    (a ≤ min a b + 1 ∧ min a b + 1 ≤ b) ∨
      (b ≤ min a b + 1 ∧ min a b + 1 ≤ a) := by
  omega

private theorem add_one_lt_of_lt_of_add_one_ne {a n : Nat}
    (ha : a < n) (hne : a + 1 ≠ n) : a + 1 < n := by
  omega

/-- Explicit row/column unit interval selected inside an ordinary component
gap. Both side endpoints are proved to lie in the same raw full component. -/
structure OrdinaryGapBoundaryCellWitness
    {component : ContactRawComponent (T := T)}
    (gap : OrdinaryComponentSpatialGap axis hn2 hT component) where
  row : Fin (n - 1)
  col : Fin (n - 1)
  componentSide : GridCellSide
  first : ↥(↑((Finset.univ : Finset (GridVertex n n)) \
    supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))
  second : ↥(↑((Finset.univ : Finset (GridVertex n n)) \
    supportFinset (gridGraph n n \ T)) : Set (GridVertex n n))
  first_mem : first ∈ component.supp
  second_mem : second ∈ component.supp
  endpoints : (gridCellBoundaryEdge row col componentSide).primalEndpoints =
    (first.1, second.1)

/-- Canonical first unit boundary segment between two noncoincident consecutive
contacts of one straight raw component. Horizontal segments use the top side
except on the bottom boundary; vertical segments use the left side except on
the right boundary. This uniformly covers indexed and mixed-side incidences. -/
noncomputable def ordinaryGapBoundaryCellWitness
    {component : ContactRawComponent (T := T)}
    (gap : OrdinaryComponentSpatialGap axis hn2 hT component) :
    OrdinaryGapBoundaryCellWitness axis hn2 hT gap := by
  let previous := componentSpatialGapPredecessor axis hn2 hT gap.1
  let current := gap.1.1
  by_cases hrow : previous.1.contact.1.1 = current.1.contact.1.1
  · have hcolNe : previous.1.contact.1.2.val ≠ current.1.contact.1.2.val := by
      intro h
      apply gap.2
      apply Prod.ext hrow
      exact Fin.ext h
    let lo := min previous.1.contact.1.2.val current.1.contact.1.2.val
    have hlo : lo + 1 < n := min_add_one_lt_of_lt_of_ne
      previous.1.contact.1.2.isLt current.1.contact.1.2.isLt hcolNe
    let firstCol : Fin n := ⟨lo, by omega⟩
    let secondCol : Fin n := ⟨lo + 1, hlo⟩
    have hfirstBetween :
        (previous.1.contact.1.2.val ≤ firstCol.val ∧
            firstCol.val ≤ current.1.contact.1.2.val) ∨
          (current.1.contact.1.2.val ≤ firstCol.val ∧
            firstCol.val ≤ previous.1.contact.1.2.val) := by
      dsimp [firstCol, lo]
      exact min_between
    have hsecondBetween :
        (previous.1.contact.1.2.val ≤ secondCol.val ∧
            secondCol.val ≤ current.1.contact.1.2.val) ∨
          (current.1.contact.1.2.val ≤ secondCol.val ∧
            secondCol.val ≤ previous.1.contact.1.2.val) := by
      dsimp [secondCol, lo]
      exact min_add_one_between hcolNe
    let firstExists := componentSpatialGap_horizontal_intermediate_mem
      axis hn2 hT gap.1 hrow firstCol hfirstBetween
    let first := Classical.choose firstExists
    have hfirst := (Classical.choose_spec firstExists).1
    have hfirstMem := (Classical.choose_spec firstExists).2
    let secondExists := componentSpatialGap_horizontal_intermediate_mem
      axis hn2 hT gap.1 hrow secondCol hsecondBetween
    let second := Classical.choose secondExists
    have hsecond := (Classical.choose_spec secondExists).1
    have hsecondMem := (Classical.choose_spec secondExists).2
    let col : Fin (n - 1) := ⟨lo, by omega⟩
    by_cases hbottom : previous.1.contact.1.1.val + 1 = n
    · let row : Fin (n - 1) := ⟨n - 2, by omega⟩
      exact
        { row := row
          col := col
          componentSide := .bottom
          first := first
          second := second
          first_mem := hfirstMem
          second_mem := hsecondMem
          endpoints := by
            rw [gridCellBoundaryEdge_primalEndpoints_bottom]
            apply Prod.ext
            · rw [hfirst]
              apply Prod.ext
              · apply Fin.ext
                change n - 2 + 1 = previous.1.contact.1.1.val
                omega
              · apply Fin.ext
                rfl
            · rw [hsecond]
              apply Prod.ext
              · apply Fin.ext
                change n - 2 + 1 = previous.1.contact.1.1.val
                omega
              · apply Fin.ext
                rfl }
    · have hrowLt : previous.1.contact.1.1.val + 1 < n :=
        add_one_lt_of_lt_of_add_one_ne previous.1.contact.1.1.isLt hbottom
      let row : Fin (n - 1) := ⟨previous.1.contact.1.1.val, by omega⟩
      exact
        { row := row
          col := col
          componentSide := .top
          first := first
          second := second
          first_mem := hfirstMem
          second_mem := hsecondMem
          endpoints := by
            rw [gridCellBoundaryEdge_primalEndpoints_top]
            apply Prod.ext
            · rw [hfirst]
              apply Prod.ext <;> apply Fin.ext <;> rfl
            · rw [hsecond]
              apply Prod.ext <;> apply Fin.ext <;> rfl }
  · have hcol : previous.1.contact.1.2 = current.1.contact.1.2 :=
      (componentSpatialGap_contacts_same_row_or_column axis hn2 hT gap.1).resolve_left
        hrow
    have hrowNe : previous.1.contact.1.1.val ≠ current.1.contact.1.1.val := by
      intro h
      apply gap.2
      apply Prod.ext
      · exact Fin.ext h
      · exact hcol
    let lo := min previous.1.contact.1.1.val current.1.contact.1.1.val
    have hlo : lo + 1 < n := min_add_one_lt_of_lt_of_ne
      previous.1.contact.1.1.isLt current.1.contact.1.1.isLt hrowNe
    let firstRow : Fin n := ⟨lo, by omega⟩
    let secondRow : Fin n := ⟨lo + 1, hlo⟩
    have hfirstBetween :
        (previous.1.contact.1.1.val ≤ firstRow.val ∧
            firstRow.val ≤ current.1.contact.1.1.val) ∨
          (current.1.contact.1.1.val ≤ firstRow.val ∧
            firstRow.val ≤ previous.1.contact.1.1.val) := by
      dsimp [firstRow, lo]
      exact min_between
    have hsecondBetween :
        (previous.1.contact.1.1.val ≤ secondRow.val ∧
            secondRow.val ≤ current.1.contact.1.1.val) ∨
          (current.1.contact.1.1.val ≤ secondRow.val ∧
            secondRow.val ≤ previous.1.contact.1.1.val) := by
      dsimp [secondRow, lo]
      exact min_add_one_between hrowNe
    let firstExists := componentSpatialGap_vertical_intermediate_mem
      axis hn2 hT gap.1 hcol firstRow hfirstBetween
    let first := Classical.choose firstExists
    have hfirst := (Classical.choose_spec firstExists).1
    have hfirstMem := (Classical.choose_spec firstExists).2
    let secondExists := componentSpatialGap_vertical_intermediate_mem
      axis hn2 hT gap.1 hcol secondRow hsecondBetween
    let second := Classical.choose secondExists
    have hsecond := (Classical.choose_spec secondExists).1
    have hsecondMem := (Classical.choose_spec secondExists).2
    let row : Fin (n - 1) := ⟨lo, by omega⟩
    by_cases hright : previous.1.contact.1.2.val + 1 = n
    · let col : Fin (n - 1) := ⟨n - 2, by omega⟩
      exact
        { row := row
          col := col
          componentSide := .right
          first := first
          second := second
          first_mem := hfirstMem
          second_mem := hsecondMem
          endpoints := by
            rw [gridCellBoundaryEdge_primalEndpoints_right]
            apply Prod.ext
            · rw [hfirst]
              apply Prod.ext
              · apply Fin.ext
                rfl
              · apply Fin.ext
                change n - 2 + 1 = previous.1.contact.1.2.val
                omega
            · rw [hsecond]
              apply Prod.ext
              · apply Fin.ext
                rfl
              · apply Fin.ext
                change n - 2 + 1 = previous.1.contact.1.2.val
                omega }
    · have hcolLt : previous.1.contact.1.2.val + 1 < n :=
        add_one_lt_of_lt_of_add_one_ne previous.1.contact.1.2.isLt hright
      let col : Fin (n - 1) := ⟨previous.1.contact.1.2.val, by omega⟩
      exact
        { row := row
          col := col
          componentSide := .left
          first := first
          second := second
          first_mem := hfirstMem
          second_mem := hsecondMem
          endpoints := by
            rw [gridCellBoundaryEdge_primalEndpoints_left]
            apply Prod.ext
            · rw [hfirst]
              apply Prod.ext <;> apply Fin.ext <;> rfl
            · rw [hsecond]
              apply Prod.ext <;> apply Fin.ext <;> rfl }

theorem OrdinaryGapBoundaryCellWitness.first_preserves
    {component : ContactRawComponent (T := T)}
    {gap : OrdinaryComponentSpatialGap axis hn2 hT component}
    (witness : OrdinaryGapBoundaryCellWitness axis hn2 hT gap) :
    preservesIncidentEdges (gridGraph n n) T witness.first.1 := by
  by_contra hnot
  exact (Finset.mem_sdiff.mp witness.first.2).2
    ((mem_supportFinset_sdiff_iff_not_preserves
      (gridGraph n n) T hT.le witness.first.1).2 hnot)

theorem OrdinaryGapBoundaryCellWitness.second_preserves
    {component : ContactRawComponent (T := T)}
    {gap : OrdinaryComponentSpatialGap axis hn2 hT component}
    (witness : OrdinaryGapBoundaryCellWitness axis hn2 hT gap) :
    preservesIncidentEdges (gridGraph n n) T witness.second.1 := by
  by_contra hnot
  exact (Finset.mem_sdiff.mp witness.second.2).2
    ((mem_supportFinset_sdiff_iff_not_preserves
      (gridGraph n n) T hT.le witness.second.1).2 hnot)

/-- Positive ordinary-gap theorem. The opposite cell side is omitted because
the component side and its two radial sides are retained. -/
def OrdinaryGapBoundaryCellWitness.transition
    {component : ContactRawComponent (T := T)}
    {gap : OrdinaryComponentSpatialGap axis hn2 hT component}
    (witness : OrdinaryGapBoundaryCellWitness axis hn2 hT gap) :
    LabelledCotreeTransition T := by
  apply gridCellOppositeLabelledCotreeTransitionOfPreservedSide hT
    witness.row witness.col witness.componentSide
  · rw [witness.endpoints]
    exact witness.first_preserves axis hn2 hT
  · rw [witness.endpoints]
    exact witness.second_preserves axis hn2 hT

/-- Exact partition of component-local spatial gaps. A gap is either
noncoincident or is the occurrence-labelled duplicated corner; no occurrence is
folded into another gap. -/
def componentSpatialGapEquivOrdinarySumDuplicatedCorner
    (component : ContactRawComponent (T := T)) :
    ComponentSpatialGap axis hn2 hT component ≃
      (OrdinaryComponentSpatialGap axis hn2 hT component ⊕
        DuplicatedCornerOverlapDebt axis hn2 hT component) :=
  let ordinary := fun gap : ComponentSpatialGap axis hn2 hT component =>
    (componentSpatialGapPredecessor axis hn2 hT gap).1.contact.1 ≠
      gap.1.1.contact.1
  (Equiv.sumCompl ordinary).symm.trans
    (Equiv.sumCongr (Equiv.refl _)
      (Equiv.subtypeEquivRight fun _ => not_ne_iff))

theorem card_componentSpatialGap_eq_ordinary_add_duplicatedCorner
    (component : ContactRawComponent (T := T)) :
    Fintype.card (ComponentSpatialGap axis hn2 hT component) =
      Fintype.card (OrdinaryComponentSpatialGap axis hn2 hT component) +
        Fintype.card (DuplicatedCornerOverlapDebt axis hn2 hT component) := by
  rw [Fintype.card_congr
    (componentSpatialGapEquivOrdinarySumDuplicatedCorner axis hn2 hT component),
    Fintype.card_sum]

/-- Distinct ordinary gaps select distinct opposite coordinate edges. Corner
occurrences are deliberately outside this physical-edge routing. -/
structure ComponentOrdinarySpatialGapRouting
    (component : ContactRawComponent (T := T)) where
  cell : ∀ gap : OrdinaryComponentSpatialGap axis hn2 hT component,
    OrdinaryGapBoundaryCellWitness axis hn2 hT gap
  edge_injective : Function.Injective fun gap =>
    gridCellBoundaryEdge (cell gap).row (cell gap).col
      (cell gap).componentSide.opposite

/-- Exact remaining local erasure theorem. The canonical witness itself is
unconditional; this proposition asks whether its occurrence labels may be
forgotten inside one component. -/
def ComponentOrdinarySpatialGapEdgeInjective
    (component : ContactRawComponent (T := T)) : Prop :=
  Function.Injective fun gap : OrdinaryComponentSpatialGap axis hn2 hT component =>
    gridCellBoundaryEdge
      (ordinaryGapBoundaryCellWitness axis hn2 hn3 hT gap).row
      (ordinaryGapBoundaryCellWitness axis hn2 hn3 hT gap).col
      (ordinaryGapBoundaryCellWitness axis hn2 hn3 hT gap).componentSide.opposite

noncomputable def componentOrdinarySpatialGapRoutingOfEdgeInjective
    (component : ContactRawComponent (T := T))
    (hinjective : ComponentOrdinarySpatialGapEdgeInjective
      axis hn2 hn3 hT component) :
    ComponentOrdinarySpatialGapRouting axis hn2 hT component where
  cell := ordinaryGapBoundaryCellWitness axis hn2 hn3 hT
  edge_injective := hinjective

/-- Unconditional occurrence-labelled ordinary-gap transition. Distinct gaps
remain distinct even in the `n = 3` mixed-boundary collision. -/
structure OrdinaryGapLabelledTransition
    (component : ContactRawComponent (T := T)) where
  gap : OrdinaryComponentSpatialGap axis hn2 hT component
  transition : LabelledCotreeTransition T

noncomputable def ordinaryGapLabelledTransition
    {component : ContactRawComponent (T := T)}
    (gap : OrdinaryComponentSpatialGap axis hn2 hT component) :
    OrdinaryGapLabelledTransition axis hn2 hT component :=
  { gap := gap
    transition := (ordinaryGapBoundaryCellWitness axis hn2 hn3 hT gap).transition
      axis hn2 hT }

theorem ordinaryGapLabelledTransition_injective
    {component : ContactRawComponent (T := T)} :
    Function.Injective
      (ordinaryGapLabelledTransition axis hn2 hn3 hT (component := component)) := by
  intro a b hab
  exact congrArg OrdinaryGapLabelledTransition.gap hab

/-- All ordinary spatial-gap occurrences, grouped by their raw component. -/
abbrev GlobalOrdinaryComponentSpatialGap :=
  Σ component : ContactRawComponent (T := T),
    OrdinaryComponentSpatialGap axis hn2 hT component

/-- Globally labelled omitted transition. The raw component and gap occurrence
are retained independently of the selected geometric edge. -/
structure GlobalOrdinaryGapLabelledTransition where
  component : ContactRawComponent (T := T)
  gap : OrdinaryComponentSpatialGap axis hn2 hT component
  transition : LabelledCotreeTransition T

noncomputable def globalOrdinaryGapLabelledTransition
    (gap : GlobalOrdinaryComponentSpatialGap axis hn2 hT) :
    GlobalOrdinaryGapLabelledTransition axis hn2 hT :=
  { component := gap.1
    gap := gap.2
    transition := (ordinaryGapBoundaryCellWitness axis hn2 hn3 hT gap.2).transition
      axis hn2 hT }

theorem globalOrdinaryGapLabelledTransition_injective :
    Function.Injective
      (globalOrdinaryGapLabelledTransition axis hn2 hn3 hT) := by
  intro a b hab
  cases a with
  | mk ac ag =>
      cases b with
      | mk bc bg =>
          have hc : ac = bc := congrArg GlobalOrdinaryGapLabelledTransition.component hab
          subst bc
          have hg : ag = bg := by
            cases hab
            rfl
          cases hg
          rfl

noncomputable def globalOrdinaryGapOccurrenceEmbedding :
    GlobalOrdinaryComponentSpatialGap axis hn2 hT ↪
      GlobalOrdinaryGapLabelledTransition axis hn2 hT where
  toFun := globalOrdinaryGapLabelledTransition axis hn2 hn3 hT
  inj' := globalOrdinaryGapLabelledTransition_injective axis hn2 hn3 hT

/-- Exact global geometric-edge erasure condition. It is intentionally
separate from occurrence-labelled routing: at `n = 3`, opposite boundary
segments can select the same central grid edge. -/
def GlobalOrdinaryGapEdgeInjective : Prop :=
  Function.Injective fun gap : GlobalOrdinaryComponentSpatialGap axis hn2 hT =>
    (globalOrdinaryGapLabelledTransition axis hn2 hn3 hT gap).transition

noncomputable def globalOrdinaryGapTransitionEmbeddingOfEdgeInjective
    (hinjective : GlobalOrdinaryGapEdgeInjective axis hn2 hn3 hT) :
    GlobalOrdinaryComponentSpatialGap axis hn2 hT ↪ LabelledCotreeTransition T where
  toFun := fun gap =>
    (globalOrdinaryGapLabelledTransition axis hn2 hn3 hT gap).transition
  inj' := hinjective

noncomputable def ComponentOrdinarySpatialGapRouting.transition
    {component : ContactRawComponent (T := T)}
    (routing : ComponentOrdinarySpatialGapRouting axis hn2 hT component)
    (gap : OrdinaryComponentSpatialGap axis hn2 hT component) :
    LabelledCotreeTransition T :=
  (routing.cell gap).transition axis hn2 hT

theorem ComponentOrdinarySpatialGapRouting.transition_injective
    {component : ContactRawComponent (T := T)}
    (routing : ComponentOrdinarySpatialGapRouting axis hn2 hT component) :
    Function.Injective (routing.transition axis hn2 hT) := by
  intro a b hab
  apply routing.edge_injective
  exact congrArg (fun edge : LabelledCotreeTransition T => edge.1) hab

/-- The southwest corner cell. -/
def southwestCornerCellRow : Fin (n - 1) := ⟨n - 2, by omega⟩

def southwestCornerCellCol : Fin (n - 1) := ⟨0, by omega⟩

/-- The northeast corner cell. -/
def northeastCornerCellRow : Fin (n - 1) := ⟨0, by omega⟩

def northeastCornerCellCol : Fin (n - 1) := ⟨n - 2, by omega⟩

/-- A deterministic omitted side of the degenerate corner cell, retaining the
original collision occurrence separately from its geometric edge. -/
structure CornerDegenerateTransition
    {component : ContactRawComponent (T := T)}
    (debt : DuplicatedCornerOverlapDebt axis hn2 hT component) where
  occurrence : ComponentSpatialGap axis hn2 hT component := debt.1
  occurrence_eq : occurrence = debt.1
  transition : LabelledCotreeTransition T

/-- The two corner attachments are retained tree sides, so acyclicity selects
one of the opposite two cell sides as a cotree transition. -/
noncomputable def cornerDegenerateTransition
    {component : ContactRawComponent (T := T)}
    (debt : DuplicatedCornerOverlapDebt axis hn2 hT component) :
    CornerDegenerateTransition axis hn2 hT debt := by
  cases axis with
  | rows =>
    have hsw :
        debt.1.1.1.contact.1.1.val + 1 = n ∧
        debt.1.1.1.contact.1.2.val = 0 ∧
        (componentSpatialGapPredecessor .rows hn2 hT debt.1).1.boundarySide
          .rows hn2 hT = .bottom ∧
        debt.1.1.1.boundarySide .rows hn2 hT = .left := by
      rcases duplicatedCornerOverlapDebt_exact .rows hn2 hT debt with h | h
      · exact h.2
      · exact (ShoreSweepAxis.noConfusion h.1)
    let previous := (componentSpatialGapPredecessor .rows hn2 hT debt.1).1
    let current := debt.1.1.1
    have hcSource : current.inwardDart.source =
        cell10 (southwestCornerCellRow hn3) (southwestCornerCellCol hn3) := by
      apply Prod.ext <;> apply Fin.ext
      · change current.contact.1.1.val = n - 2 + 1
        have hv : current.contact.1.1.val + 1 = n := hsw.1
        omega
      · change current.contact.1.2.val = 0
        exact hsw.2.1
    have hpSource : previous.inwardDart.source =
        cell10 (southwestCornerCellRow hn3) (southwestCornerCellCol hn3) := by
      rw [show previous.inwardDart.source = current.inwardDart.source by
        exact debt.2]
      exact hcSource
    have hpDirection : previous.inwardDart.direction = .north := by
      change (previous.boundarySide .rows hn2 hT).inwardDirection = .north
      rw [hsw.2.2.1]
      rfl
    have hcDirection : current.inwardDart.direction = .east := by
      change (current.boundarySide .rows hn2 hT).inwardDirection = .east
      rw [hsw.2.2.2]
      rfl
    have hpTarget : previous.inwardDart.target =
        cell00 (southwestCornerCellRow hn3) (southwestCornerCellCol hn3) := by
      have hs := previous.inwardDart.step
      rw [hpSource, hpDirection] at hs
      have hneighbor : gridNeighbor?
          (cell10 (southwestCornerCellRow hn3) (southwestCornerCellCol hn3))
          .north = some
            (cell00 (southwestCornerCellRow hn3) (southwestCornerCellCol hn3)) := by
        simp [southwestCornerCellRow, southwestCornerCellCol, cell10, cell00,
          gridNeighbor?]
      rw [hneighbor] at hs
      exact (Option.some.inj hs).symm
    have hcTarget : current.inwardDart.target =
        cell11 (southwestCornerCellRow hn3) (southwestCornerCellCol hn3) := by
      have hs := current.inwardDart.step
      rw [hcSource, hcDirection] at hs
      have hneighbor : gridNeighbor?
          (cell10 (southwestCornerCellRow hn3) (southwestCornerCellCol hn3))
          .east = some
            (cell11 (southwestCornerCellRow hn3) (southwestCornerCellCol hn3)) := by
        simp [southwestCornerCellRow, southwestCornerCellCol, cell10, cell11,
          gridNeighbor?]
        omega
      rw [hneighbor] at hs
      exact (Option.some.inj hs).symm
    exact
      { occurrence := debt.1
        occurrence_eq := rfl
        transition :=
          gridCellTopElseRightCotreeTransitionOfBottomLeftRetained hT
            (southwestCornerCellRow hn3) (southwestCornerCellCol hn3)
            (by simpa [hcTarget, hcSource] using current.inwardDart.adj.symm)
            (by simpa [hpTarget, hpSource] using previous.inwardDart.adj) }
  | columns =>
    have hne :
        debt.1.1.1.contact.1.1.val = 0 ∧
        debt.1.1.1.contact.1.2.val + 1 = n ∧
        (componentSpatialGapPredecessor .columns hn2 hT debt.1).1.boundarySide
          .columns hn2 hT = .top ∧
        debt.1.1.1.boundarySide .columns hn2 hT = .right := by
      rcases duplicatedCornerOverlapDebt_exact .columns hn2 hT debt with h | h
      · exact (ShoreSweepAxis.noConfusion h.1)
      · exact h.2
    let previous := (componentSpatialGapPredecessor .columns hn2 hT debt.1).1
    let current := debt.1.1.1
    have hcSource : current.inwardDart.source =
        cell01 (northeastCornerCellRow hn3) (northeastCornerCellCol hn3) := by
      apply Prod.ext <;> apply Fin.ext
      · change current.contact.1.1.val = 0
        exact hne.1
      · change current.contact.1.2.val = n - 2 + 1
        have hv : current.contact.1.2.val + 1 = n := hne.2.1
        omega
    have hpSource : previous.inwardDart.source =
        cell01 (northeastCornerCellRow hn3) (northeastCornerCellCol hn3) := by
      rw [show previous.inwardDart.source = current.inwardDart.source by
        exact debt.2]
      exact hcSource
    have hpDirection : previous.inwardDart.direction = .south := by
      change (previous.boundarySide .columns hn2 hT).inwardDirection = .south
      rw [hne.2.2.1]
      rfl
    have hcDirection : current.inwardDart.direction = .west := by
      change (current.boundarySide .columns hn2 hT).inwardDirection = .west
      rw [hne.2.2.2]
      rfl
    have hpTarget : previous.inwardDart.target =
        cell11 (northeastCornerCellRow hn3) (northeastCornerCellCol hn3) := by
      have hs := previous.inwardDart.step
      rw [hpSource, hpDirection] at hs
      have hneighbor : gridNeighbor?
          (cell01 (northeastCornerCellRow hn3) (northeastCornerCellCol hn3))
          .south = some
            (cell11 (northeastCornerCellRow hn3) (northeastCornerCellCol hn3)) := by
        simp [northeastCornerCellRow, northeastCornerCellCol, cell01, cell11,
          gridNeighbor?]
        omega
      rw [hneighbor] at hs
      exact (Option.some.inj hs).symm
    have hcTarget : current.inwardDart.target =
        cell00 (northeastCornerCellRow hn3) (northeastCornerCellCol hn3) := by
      have hs := current.inwardDart.step
      rw [hcSource, hcDirection] at hs
      have hneighbor : gridNeighbor?
          (cell01 (northeastCornerCellRow hn3) (northeastCornerCellCol hn3))
          .west = some
            (cell00 (northeastCornerCellRow hn3) (northeastCornerCellCol hn3)) := by
        simp [northeastCornerCellRow, northeastCornerCellCol, cell01, cell00,
          gridNeighbor?]
      rw [hneighbor] at hs
      exact (Option.some.inj hs).symm
    exact
      { occurrence := debt.1
        occurrence_eq := rfl
        transition :=
          gridCellBottomElseLeftCotreeTransitionOfTopRightRetained hT
            (northeastCornerCellRow hn3) (northeastCornerCellCol hn3)
            (by simpa [hcTarget, hcSource] using current.inwardDart.adj.symm)
            (by simpa [hpTarget, hpSource] using previous.inwardDart.adj) }

/-- Sum tags preserve the corner occurrence even when its selected coordinate
edge happens to equal an ordinary-gap transition. -/
theorem ordinaryGapOccurrence_ne_cornerOccurrence
    {component : ContactRawComponent (T := T)}
    (ordinary : OrdinaryComponentSpatialGap axis hn2 hT component)
    (corner : DuplicatedCornerOverlapDebt axis hn2 hT component) :
    (Sum.inl ordinary : OrdinaryComponentSpatialGap axis hn2 hT component ⊕
      DuplicatedCornerOverlapDebt axis hn2 hT component) ≠ Sum.inr corner := by
  simp

/-- Ordinary and corner omitted-edge occurrences for one raw component. -/
abbrev ComponentOmittedEdgeOccurrence
    (component : ContactRawComponent (T := T)) :=
  OrdinaryComponentSpatialGap axis hn2 hT component ⊕
    DuplicatedCornerOverlapDebt axis hn2 hT component

/-- The cotree transition selected by a component-local omitted-edge
occurrence. Coordinate collisions may exist before any use of tree acyclicity;
they are irrelevant here because the occurrence label is retained. -/
noncomputable def componentOmittedEdgeTransition
    {component : ContactRawComponent (T := T)}
    (occurrence : ComponentOmittedEdgeOccurrence axis hn2 hT component) :
    LabelledCotreeTransition T :=
  match occurrence with
  | .inl gap => (ordinaryGapBoundaryCellWitness axis hn2 hn3 hT gap).transition
      axis hn2 hT
  | .inr debt => (cornerDegenerateTransition axis hn2 hn3 hT debt).transition

/-- The omitted edge paired with its exact ordinary/corner occurrence. -/
structure ComponentLabelledOmittedEdge
    (component : ContactRawComponent (T := T)) where
  occurrence : ComponentOmittedEdgeOccurrence axis hn2 hT component
  transition : LabelledCotreeTransition T

noncomputable def componentLabelledOmittedEdge
    {component : ContactRawComponent (T := T)}
    (occurrence : ComponentOmittedEdgeOccurrence axis hn2 hT component) :
    ComponentLabelledOmittedEdge axis hn2 hT component :=
  { occurrence := occurrence
    transition := componentOmittedEdgeTransition axis hn2 hn3 hT occurrence }

theorem componentLabelledOmittedEdge_injective
    {component : ContactRawComponent (T := T)} :
    Function.Injective
      (componentLabelledOmittedEdge axis hn2 hn3 hT (component := component)) := by
  intro a b hab
  exact congrArg ComponentLabelledOmittedEdge.occurrence hab

/-- Reindex every spatial gap as an occurrence-labelled omitted edge. -/
noncomputable def componentOmittedEdgeEmbedding
    {component : ContactRawComponent (T := T)}
    : ComponentSpatialGap axis hn2 hT component ↪
      ComponentLabelledOmittedEdge axis hn2 hT component :=
  (componentSpatialGapEquivOrdinarySumDuplicatedCorner axis hn2 hT component).toEmbedding.trans
    { toFun := componentLabelledOmittedEdge axis hn2 hn3 hT
      inj' := componentLabelledOmittedEdge_injective axis hn2 hn3 hT }

theorem rankedCarrierGapSpatialCandidates_nonempty_of_contact_ne
    (gap : RankedCarrierGapWitness axis hn2 hT)
    (hne : gap.previous.contact.1 ≠ gap.current.1.contact.1) :
    (rankedCarrierGapSpatialCandidates axis hn2 hT gap).Nonempty := by
  refine ⟨gap.previous, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  have hcomponent : gap.previous.component = gap.current.1.component := by
    rw [gap.previous_eq]
    exact rankedCarrierGapPredecessor_component axis hn2 hT gap.current
  exact ⟨hcomponent, hne, by omega, by omega⟩

/-- Nearest canonical contact to the current contact inside the spatial segment.
This replaces the contour predecessor whenever intervening canonical contacts
exist spatially. -/
noncomputable def rankedCarrierGapSpatialPredecessor
    (gap : RankedCarrierGapWitness axis hn2 hT)
    (hne : gap.previous.contact.1 ≠ gap.current.1.contact.1) :
    ContactEnrichedCanonicalMergerToken axis hn2 hT :=
  Classical.choose (Finset.exists_min_image
    (rankedCarrierGapSpatialCandidates axis hn2 hT gap)
    (fun token => contactGridDistance axis hn2 hT token gap.current.1)
    (rankedCarrierGapSpatialCandidates_nonempty_of_contact_ne
      axis hn2 hT gap hne))

theorem rankedCarrierGapSpatialPredecessor_mem
    (gap : RankedCarrierGapWitness axis hn2 hT)
    (hne : gap.previous.contact.1 ≠ gap.current.1.contact.1) :
    rankedCarrierGapSpatialPredecessor axis hn2 hT gap hne ∈
      rankedCarrierGapSpatialCandidates axis hn2 hT gap :=
  (Classical.choose_spec (Finset.exists_min_image
    (rankedCarrierGapSpatialCandidates axis hn2 hT gap)
    (fun token => contactGridDistance axis hn2 hT token gap.current.1)
    (rankedCarrierGapSpatialCandidates_nonempty_of_contact_ne
      axis hn2 hT gap hne))).1

theorem rankedCarrierGapSpatialPredecessor_distance_minimal
    (gap : RankedCarrierGapWitness axis hn2 hT)
    (hne : gap.previous.contact.1 ≠ gap.current.1.contact.1)
    {other : ContactEnrichedCanonicalMergerToken axis hn2 hT}
    (hother : other ∈ rankedCarrierGapSpatialCandidates axis hn2 hT gap) :
    contactGridDistance axis hn2 hT
        (rankedCarrierGapSpatialPredecessor axis hn2 hT gap hne) gap.current.1 ≤
      contactGridDistance axis hn2 hT other gap.current.1 :=
  (Classical.choose_spec (Finset.exists_min_image
    (rankedCarrierGapSpatialCandidates axis hn2 hT gap)
    (fun token => contactGridDistance axis hn2 hT token gap.current.1)
    (rankedCarrierGapSpatialCandidates_nonempty_of_contact_ne
      axis hn2 hT gap hne))).2 other hother

/-- Spatial refinement still retains the original collision injectively because
the current enriched token is retained in the pair. -/
def rankedCarrierCollisionSpatialGapEmbedding :
    RankedContactEnrichedCarrierCollision axis hn2 hT ↪
      (ContactEnrichedCanonicalMergerToken axis hn2 hT ×
        ContactEnrichedCanonicalMergerToken axis hn2 hT) where
  toFun collision :=
    let gap := rankedCarrierGapWitness axis hn2 hT collision
    if hne : gap.previous.contact.1 ≠ gap.current.1.contact.1 then
      (rankedCarrierGapSpatialPredecessor axis hn2 hT gap hne, gap.current.1)
    else
      (gap.previous, gap.current.1)
  inj' := by
    intro a b hab
    apply Subtype.ext
    have hcurrent := congrArg Prod.snd hab
    dsimp only at hcurrent
    split at hcurrent <;> split at hcurrent <;> exact hcurrent

/-- A deterministic boundary-adjacent cell and its side opposite the free
boundary interval.  The opposite edge has both endpoints in cotree support,
so it has an exact internal-or-labelled-cotree dichotomy without any leaf
degree assumption. -/
structure BoundaryCellGap
    {n : Nat} {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj] where
  row : Fin (n - 1)
  col : Fin (n - 1)
  boundarySide : GridCellSide
  fourthSide : GridCellSide
  sides_ne : boundarySide ≠ fourthSide
  fourth_first_supported :
    (gridCellBoundaryEdge row col fourthSide).primalEndpoints.1 ∈
      supportFinset (gridGraph n n \ T)
  fourth_second_supported :
    (gridCellBoundaryEdge row col fourthSide).primalEndpoints.2 ∈
      supportFinset (gridGraph n n \ T)

/-- Coordinate-only boundary cell address.  Unlike `BoundaryCellGap`, this
does not assert that the chosen fourth side is physically supported. -/
structure BoundaryCellAddress where
  row : Fin (n - 1)
  col : Fin (n - 1)
  boundarySide : GridCellSide
  fourthSide : GridCellSide
  sides_ne : boundarySide ≠ fourthSide

/-- Occurrence-labelled address.  The current enriched token is retained until
physical edge injectivity has actually been proved. -/
structure RankedCarrierBoundaryCellOccurrence where
  current : ContactEnrichedCanonicalMergerToken axis hn2 hT
  address : BoundaryCellAddress (n := n)

/-- Forgetting to the coordinate cell is intentionally a separate map; it need
not be injective at corners or when several collision intervals choose the same
boundary-adjacent cell. -/
def RankedCarrierBoundaryCellOccurrence.cell
    (occurrence : RankedCarrierBoundaryCellOccurrence axis hn2 hT) :=
  (occurrence.address.row, occurrence.address.col)

/-- Any deterministic address assignment gives an injective occurrence map by
retaining the collision's current enriched token. -/
def rankedCarrierCollisionBoundaryCellOccurrenceEmbedding
    (address : RankedContactEnrichedCarrierCollision axis hn2 hT →
      BoundaryCellAddress (n := n)) :
    RankedContactEnrichedCarrierCollision axis hn2 hT ↪
      RankedCarrierBoundaryCellOccurrence axis hn2 hT where
  toFun collision := ⟨collision.1, address collision⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg RankedCarrierBoundaryCellOccurrence.current hab

/-- Exact strengthening required to erase occurrence labels at the cell level. -/
def BoundaryCellAddressInjective
    (address : RankedContactEnrichedCarrierCollision axis hn2 hT →
      BoundaryCellAddress (n := n)) : Prop :=
  Function.Injective fun collision =>
    ((address collision).row, (address collision).col)

/-- Exact strengthening required to erase occurrence labels at the selected
edge level.  It is stronger than coordinate-cell injectivity because distinct
cell/side pairs may represent the same shared grid edge. -/
def BoundaryCellEdgeInjective
    (address : RankedContactEnrichedCarrierCollision axis hn2 hT →
      BoundaryCellAddress (n := n)) : Prop :=
  Function.Injective fun collision =>
    gridCellBoundaryEdge (address collision).row (address collision).col
      (address collision).fourthSide

/-- Physical support gate converting an address into the fixed-side cell
dichotomy. -/
def BoundaryCellAddress.PhysicallySupported
    (address : BoundaryCellAddress (n := n)) : Prop :=
  (gridCellBoundaryEdge address.row address.col
      address.fourthSide).primalEndpoints.1 ∈
      supportFinset (gridGraph n n \ T) ∧
    (gridCellBoundaryEdge address.row address.col
      address.fourthSide).primalEndpoints.2 ∈
      supportFinset (gridGraph n n \ T)

def BoundaryCellGap.ofAddress
    (address : BoundaryCellAddress (n := n))
    (hsupported : address.PhysicallySupported (T := T)) :
    BoundaryCellGap (T := T) where
  row := address.row
  col := address.col
  boundarySide := address.boundarySide
  fourthSide := address.fourthSide
  sides_ne := address.sides_ne
  fourth_first_supported := hsupported.1
  fourth_second_supported := hsupported.2

/-- The exact, fixed-side alternative of a boundary-cell gap. -/
noncomputable def BoundaryCellGap.alternative
    (gap : BoundaryCellGap (T := T)) :
    ↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))) ⊕
      LabelledCotreeTransition T := by
  classical
  let edge := gridCellBoundaryEdge gap.row gap.col gap.fourthSide
  if hadj : T.Adj edge.primalEndpoints.1 edge.primalEndpoints.2 then
    exact .inl ⟨edge.primalSym2,
      gridCellBoundaryEdge_mem_internalEdgeFinset_of_supported T gap.row gap.col
        gap.fourthSide hadj gap.fourth_first_supported gap.fourth_second_supported⟩
  else
    exact .inr ⟨edge, (gridCellBoundaryEdge_mem_cotree_iff
      T gap.row gap.col gap.fourthSide).2 hadj⟩

theorem BoundaryCellGap.alternative_edge
    (gap : BoundaryCellGap (T := T)) :
    match gap.alternative with
    | .inl edge => edge.1 =
        (gridCellBoundaryEdge gap.row gap.col gap.fourthSide).primalSym2
    | .inr edge => edge.1 =
        gridCellBoundaryEdge gap.row gap.col gap.fourthSide := by
  classical
  rcases hresult : gap.alternative with edge | edge
  · change edge.1 = _
    unfold BoundaryCellGap.alternative at hresult
    dsimp only at hresult
    split at hresult
    · exact congrArg Subtype.val (Sum.inl.inj hresult).symm
    · contradiction
  · change edge.1 = _
    unfold BoundaryCellGap.alternative at hresult
    dsimp only at hresult
    split at hresult
    · contradiction
    · exact congrArg Subtype.val (Sum.inr.inj hresult).symm

/-- Honest outcome kind of boundary-cell classification. -/
inductive RankedCarrierBoundaryCellKind where
  | distinctSameSide
  | coincident
  | mixedSide
  deriving DecidableEq

/-- Occurrence-labelled boundary-cell result.  The optional physical cell is
present exactly in the proved same-side branch.  Current-token and orientation
labels remain available in `gap`, so coincident corner incidences cannot be
identified with noncoincident gaps. -/
structure RankedCarrierBoundaryCellClassification
    {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) where
  gap : RankedCarrierGapWitness axis hn2 hT
  spatialPrevious : ContactEnrichedCanonicalMergerToken axis hn2 hT
  kind : RankedCarrierBoundaryCellKind
  cell : Option (BoundaryCellGap (T := T))

/-- Proof obligations attached to a boundary-cell classification. -/
def RankedCarrierBoundaryCellClassification.Valid
    (classification : RankedCarrierBoundaryCellClassification axis hn2 hT) : Prop :=
  classification.spatialPrevious.component = classification.gap.current.1.component ∧
  (classification.cell.isSome ↔ classification.kind = .distinctSameSide) ∧
  (classification.kind = .distinctSameSide →
    classification.spatialPrevious.contact.1 ≠ classification.gap.current.1.contact.1 ∧
    classification.spatialPrevious.boundarySide axis hn2 hT =
      classification.gap.current.1.boundarySide axis hn2 hT) ∧
  (classification.kind = .coincident →
    classification.gap.previous.contact.1 = classification.gap.current.1.contact.1 ∧
    classification.gap.previous.attachmentOrientation ≠
      classification.gap.current.1.attachmentOrientation) ∧
  (classification.kind = .mixedSide →
    classification.spatialPrevious.contact.1 ≠ classification.gap.current.1.contact.1 ∧
    classification.spatialPrevious.boundarySide axis hn2 hT ≠
      classification.gap.current.1.boundarySide axis hn2 hT)

/-- Only the same-side branch has a proved physical cell alternative. -/
def RankedCarrierBoundaryCellClassification.alternative?
    {n : Nat} {axis : ShoreSweepAxis} {hn2 : 2 ≤ n}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    {hT : IsSpanningSubtree (gridGraph n n) T} :
    RankedCarrierBoundaryCellClassification axis hn2 hT →
      Option (↥(internalEdgeFinset T
          (supportFinset (gridGraph n n \ T))) ⊕ LabelledCotreeTransition T)
  | classification => classification.cell.map BoundaryCellGap.alternative

/-- Exact remaining geometric construction.  Same-side distinct contacts must
produce the fixed opposite-side boundary cell; coincident and mixed-side cases
are retained honestly rather than assigned an unproved physical payment. -/
def RankedCarrierBoundaryCellResidual
    {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) : Prop :=
  ∀ gap : RankedCarrierGapWitness axis hn2 hT,
    ∃ classification : RankedCarrierBoundaryCellClassification axis hn2 hT,
      classification.gap = gap ∧ classification.Valid axis hn2 hT

/-- Fully explicit residual needed to turn boundary-cell occurrences into
globally distinct physical alternatives.  No cardinality assertion is hidden
here: each field is a geometric support or injectivity statement. -/
structure RankedCarrierBoundaryCellRoutingData where
  address : RankedContactEnrichedCarrierCollision axis hn2 hT →
    BoundaryCellAddress (n := n)
  supported : ∀ collision, (address collision).PhysicallySupported (T := T)
  edge_injective : BoundaryCellEdgeInjective axis hn2 hT address

/-- Routing data gives the exact fixed-side internal/cotree alternative for
every collision. -/
noncomputable def RankedCarrierBoundaryCellRoutingData.alternative
    (data : RankedCarrierBoundaryCellRoutingData axis hn2 hT)
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT) :
    ↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T))) ⊕
      LabelledCotreeTransition T :=
  (BoundaryCellGap.ofAddress (data.address collision)
    (data.supported collision)).alternative

theorem RankedCarrierBoundaryCellRoutingData.alternative_edge
    (data : RankedCarrierBoundaryCellRoutingData axis hn2 hT)
    (collision : RankedContactEnrichedCarrierCollision axis hn2 hT) :
    match data.alternative axis hn2 hT collision with
    | .inl edge => edge.1 =
        (gridCellBoundaryEdge (data.address collision).row
          (data.address collision).col
          (data.address collision).fourthSide).primalSym2
    | .inr edge => edge.1 =
        gridCellBoundaryEdge (data.address collision).row
          (data.address collision).col
          (data.address collision).fourthSide :=
  (BoundaryCellGap.ofAddress (data.address collision)
    (data.supported collision)).alternative_edge

/-- Injective selected coordinate edges make the classified physical
alternatives injective, independently of which edges are retained by the tree. -/
theorem RankedCarrierBoundaryCellRoutingData.alternative_injective
    (data : RankedCarrierBoundaryCellRoutingData axis hn2 hT) :
    Function.Injective (data.alternative axis hn2 hT) := by
  intro a b hab
  have hedge : gridCellBoundaryEdge (data.address a).row (data.address a).col
        (data.address a).fourthSide =
      gridCellBoundaryEdge (data.address b).row (data.address b).col
        (data.address b).fourthSide := by
    cases ha : data.alternative axis hn2 hT a with
    | inl edgeA =>
        cases hb : data.alternative axis hn2 hT b with
        | inl edgeB =>
            have hvalues : edgeA.1 = edgeB.1 := by
              rw [ha, hb] at hab
              exact congrArg Subtype.val (Sum.inl.inj hab)
            apply GridEdge.primalSym2_injective
            have hea := data.alternative_edge axis hn2 hT a
            have heb := data.alternative_edge axis hn2 hT b
            rw [ha] at hea
            rw [hb] at heb
            exact hea.symm.trans (hvalues.trans heb)
        | inr edgeB => simp [ha, hb] at hab
    | inr edgeA =>
        cases hb : data.alternative axis hn2 hT b with
        | inl edgeB => simp [ha, hb] at hab
        | inr edgeB =>
            have hvalues : edgeA.1 = edgeB.1 := by
              rw [ha, hb] at hab
              exact congrArg Subtype.val (Sum.inr.inj hab)
            have hea := data.alternative_edge axis hn2 hT a
            have heb := data.alternative_edge axis hn2 hT b
            rw [ha] at hea
            rw [hb] at heb
            exact hea.symm.trans (hvalues.trans heb)
  exact data.edge_injective hedge


/-- A coincident outside contact is not itself a split outer-port vertex. -/
theorem rankedCarrierGap_coincident_contact_not_splitOuterPort
    (gap : RankedCarrierGapWitness axis hn2 hT)
    (_hcontact : gap.previous.contact.1 = gap.current.1.contact.1)
    (port : GridCotreeOuterPort T) :
    port.vertex ≠ gap.previous.contact.1 := by
  intro heq
  apply CanonicalShoreDemand.unsupported_boundary_not_mem_support
    axis hn2 T gap.previous.unsupportedDemand
  rw [← gap.previous.contact_eq_boundaryIncidence axis hn2 hT, ← heq]
  exact port.vertex_mem

/-- The retained attachment of either enriched token is noninternal because
its explicit contact endpoint is outside cotree support. -/
theorem contactEnrichedCanonicalMergerToken_attachment_not_internal
    (token : ContactEnrichedCanonicalMergerToken axis hn2 hT) :
    ¬TreeEdgeTokenIsInternal (supportFinset (gridGraph n n \ T))
      (mergerSlotTreeEdgeEmbedding axis hn2 hn3 hT) token.mergerSlot :=
  mergerSlotTreeEdgeEmbedding_isNoninternal axis hn2 hn3 hT token.mergerSlot

/-- Carrier classes of canonical merger tokens, represented in contour order. -/
abbrev OrderedCanonicalMergerCarrierQuotient :=
  CarrierQuotient (canonicalMergerTokenCarrier axis hn2 hn3 hT)

/-- Canonical merger tokens that are not the first token of their carrier in
forward expanded-contour order. -/
abbrev OrderedCanonicalMergerCollision :=
  RankedCarrierCollision (canonicalMergerTokenCarrier axis hn2 hn3 hT)
    (canonicalMergerForwardRank axis hn2 hT)

/-- First canonical merger token in a carrier class in forward contour order. -/
def orderedCanonicalMergerRepresentative
    (q : OrderedCanonicalMergerCarrierQuotient axis hn2 hn3 hT) :
    (planeChannelForest axis hn2 hT).forest.MergerSlot :=
  rankedCarrierRepresentative (canonicalMergerTokenCarrier axis hn2 hn3 hT)
    (canonicalMergerForwardRank axis hn2 hT) q

@[simp] theorem orderedCanonicalMergerRepresentative_represents
    (q : OrderedCanonicalMergerCarrierQuotient axis hn2 hn3 hT) :
    carrierQuotientMk (canonicalMergerTokenCarrier axis hn2 hn3 hT)
      (orderedCanonicalMergerRepresentative axis hn2 hn3 hT q) = q :=
  carrierQuotientMk_rankedCarrierRepresentative _ _ q

/-- The ordered canonical representative is the unique minimum-rank token in
its component carrier class. -/
theorem eq_orderedCanonicalMergerRepresentative_of_minimal
    (q : OrderedCanonicalMergerCarrierQuotient axis hn2 hn3 hT)
    {s : (planeChannelForest axis hn2 hT).forest.MergerSlot}
    (hs : carrierQuotientMk (canonicalMergerTokenCarrier axis hn2 hn3 hT) s = q)
    (hmin : ∀ t,
      carrierQuotientMk (canonicalMergerTokenCarrier axis hn2 hn3 hT) t = q ->
        canonicalMergerForwardRank axis hn2 hT s ≤
          canonicalMergerForwardRank axis hn2 hT t) :
    s = orderedCanonicalMergerRepresentative axis hn2 hn3 hT q :=
  eq_rankedCarrierRepresentative_of_minimal _ _
    (canonicalMergerForwardRank_injective axis hn2 hT) q hs hmin

/-- Exact ordered split of canonical merger tokens into carrier classes and
all later same-carrier occurrences. -/
def orderedCanonicalMergerCarrierEquiv :
    (planeChannelForest axis hn2 hT).forest.MergerSlot ≃
      OrderedCanonicalMergerCarrierQuotient axis hn2 hn3 hT ⊕
        OrderedCanonicalMergerCollision axis hn2 hn3 hT :=
  rankedCarrierQuotientCollisionEquiv
    (canonicalMergerTokenCarrier axis hn2 hn3 hT)
    (canonicalMergerForwardRank axis hn2 hT)

/-- Exact cardinal accounting for ordered canonical merger collisions. -/
theorem card_orderedCanonicalMergerCarrier_add_collision :
    Fintype.card (planeChannelForest axis hn2 hT).forest.MergerSlot =
      Fintype.card (OrderedCanonicalMergerCarrierQuotient axis hn2 hn3 hT) +
        Fintype.card (OrderedCanonicalMergerCollision axis hn2 hn3 hT) :=
  card_carrierQuotient_add_card_rankedCollision _ _

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
