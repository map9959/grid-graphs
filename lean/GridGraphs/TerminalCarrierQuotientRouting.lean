import GridGraphs.ChannelCarrierRoots
import GridGraphs.ChannelContourRouting
import GridGraphs.TreeEdgeMergerResources
import GridGraphs.LocalizedHallRouting

/-!
# Terminal carrier quotient accounting

This file contains only finite accounting.  It does not assert that the
required complementary-resource routing exists in a geometric realization.
The root-only API at the end of the file is more generic, but requires an
explicit cotree contact for every surviving root.  The physical-token API
instead reserves the resources canonically determined by tree-edge tokens.
-/

namespace GridGraphs

open Finset SimpleGraph

universe u v w

variable {A : Type u} {K : Type v}

/-- Occurrences are equivalent when they have the same carrier. -/
def carrierSetoid (carrier : A -> K) : Setoid A :=
  Setoid.ker carrier

/-- The finite occurrence quotient by equality of carrier. -/
abbrev CarrierQuotient (carrier : A -> K) :=
  Quotient (carrierSetoid carrier)

/-- The carrier class of an occurrence. -/
def carrierQuotientMk (carrier : A -> K) (a : A) : CarrierQuotient carrier :=
  Quotient.mk _ a

noncomputable instance carrierQuotientFintype [Fintype A] (carrier : A -> K) :
    Fintype (CarrierQuotient carrier) := by
  classical
  exact Fintype.ofSurjective (carrierQuotientMk carrier) Quotient.exists_rep

/-- The carrier represented by a quotient class. -/
def carrierQuotientEmbedding (carrier : A -> K) : CarrierQuotient carrier ↪ K where
  toFun := Quotient.lift carrier (fun _ _ h => h)
  inj' := by
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro a b hab
    exact Quotient.sound hab

@[simp] theorem carrierQuotientEmbedding_mk (carrier : A → K) (a : A) :
    carrierQuotientEmbedding carrier (carrierQuotientMk carrier a) = carrier a :=
  rfl

/-- A fixed representative occurrence for each carrier class. -/
noncomputable def carrierRepresentative (carrier : A -> K)
    (q : CarrierQuotient carrier) : A :=
  Classical.choose q.exists_rep

@[simp] theorem carrierQuotientMk_representative (carrier : A -> K)
    (q : CarrierQuotient carrier) :
    carrierQuotientMk carrier (carrierRepresentative carrier q) = q :=
  Classical.choose_spec q.exists_rep

/-- Nonrepresentative occurrences, retaining their original occurrence label. -/
def CarrierCollision (carrier : A -> K) :=
  {a : A // Not (a = carrierRepresentative carrier (carrierQuotientMk carrier a))}

noncomputable instance carrierCollisionFintype [Fintype A] (carrier : A -> K) :
    Fintype (CarrierCollision carrier) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Every occurrence is either the selected representative of its carrier
class or a collision carrying its original label. -/
noncomputable def carrierQuotientCollisionEquiv (carrier : A -> K) :
    A ≃ (CarrierQuotient carrier ⊕ CarrierCollision carrier) := by
  classical
  refine
    { toFun := fun a =>
        if h : a = carrierRepresentative carrier (carrierQuotientMk carrier a)
        then Sum.inl (carrierQuotientMk carrier a)
        else Sum.inr ⟨a, h⟩
      invFun := fun x => match x with
        | Sum.inl q => carrierRepresentative carrier q
        | Sum.inr a => a.1
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    by_cases h : a = carrierRepresentative carrier (carrierQuotientMk carrier a)
    · dsimp
      rw [dif_pos h]
      exact h.symm
    · dsimp
      rw [dif_neg h]
  · intro x
    rcases x with q | a
    · dsimp
      have hmk := carrierQuotientMk_representative carrier q
      have hrep : carrierRepresentative carrier q =
          carrierRepresentative carrier
            (carrierQuotientMk carrier (carrierRepresentative carrier q)) :=
        congrArg (carrierRepresentative carrier) hmk.symm
      rw [dif_pos hrep]
      exact congrArg Sum.inl hmk
    · dsimp
      rw [dif_neg a.property]
      exact congrArg Sum.inr (Subtype.ext rfl)

/-- Exact finite accounting for carrier classes and labelled collisions. -/
theorem card_carrierQuotient_add_card_collision [Fintype A] (carrier : A -> K) :
    Fintype.card A =
      Fintype.card (CarrierQuotient carrier) + Fintype.card (CarrierCollision carrier) := by
  classical
  rw [Fintype.card_congr (carrierQuotientCollisionEquiv carrier), Fintype.card_sum]

section RootPortMultiplicity

variable {V P : Type*} [Fintype V] [DecidableEq V] [DecidableEq P]
  (F : ParentForest V) (rootPort : ↥F.roots → P)

/-- The carrier quotient of roots by port is exactly the finite set of used
ports.  This identifies the representative convention used by quotient
reservations with the representative-per-used-port convention in the forest
ledger. -/
noncomputable def rootPortCarrierQuotientEquivUsedRootPorts :
    CarrierQuotient rootPort ≃ ↥(F.usedRootPorts rootPort) := by
  classical
  let rootOf : ↥(F.usedRootPorts rootPort) → ↥F.roots := fun port =>
    Classical.choose (Finset.mem_image.mp port.2)
  have rootOf_spec : ∀ port, rootPort (rootOf port) = port.1 := fun port =>
    (Classical.choose_spec (Finset.mem_image.mp port.2)).2
  refine
    { toFun := fun q => ⟨carrierQuotientEmbedding rootPort q, ?_⟩
      invFun := fun port => carrierQuotientMk rootPort (rootOf port)
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨root, rfl⟩ := q.exists_rep
    exact Finset.mem_image.mpr ⟨root, Finset.mem_univ _, rfl⟩
  · intro q
    apply (carrierQuotientEmbedding rootPort).injective
    change rootPort (rootOf _) = carrierQuotientEmbedding rootPort q
    exact rootOf_spec _
  · intro port
    apply Subtype.ext
    change rootPort (rootOf port) = port.1
    exact rootOf_spec port

/-- Duplicate-root debt slots are merely another labelling of the
nonrepresentative roots selected by the carrier quotient. -/
noncomputable def rootPortDebtSlotEquivCarrierCollision :
    F.RootPortDebtSlot rootPort ≃ CarrierCollision rootPort := by
  apply Fintype.equivOfCardEq
  have hroots := F.card_usedRootPorts_add_rootPortDebt rootPort
  have hcarrier := card_carrierQuotient_add_card_collision rootPort
  have hused : Fintype.card (CarrierQuotient rootPort) =
      (F.usedRootPorts rootPort).card := by
    rw [Fintype.card_congr
      (rootPortCarrierQuotientEquivUsedRootPorts F rootPort), Fintype.card_coe]
  rw [F.card_rootPortDebtSlot]
  apply Nat.add_left_cancel (n := (F.usedRootPorts rootPort).card)
  calc
    (F.usedRootPorts rootPort).card + F.rootPortDebt rootPort = F.roots.card :=
      hroots
    _ = Fintype.card (CarrierQuotient rootPort) +
        Fintype.card (CarrierCollision rootPort) := by
          rw [← Fintype.card_coe]
          exact hcarrier
    _ = (F.usedRootPorts rootPort).card +
        Fintype.card (CarrierCollision rootPort) := by rw [hused]

/-- If surviving roots have distinct component labels, every duplicate port
slot uses the component of its nonrepresentative root.  Distinct slots remain
distinct, and no image is the component selected for the quotient
representative of any used port. -/
noncomputable def rootPortDebtSlotComponentEmbedding
    {K : Type*} (rootComponent : ↥F.roots → K)
    (hcomponent : Function.Injective rootComponent) :
    F.RootPortDebtSlot rootPort ↪
      {k : K // k ∉ Set.range (fun q : CarrierQuotient rootPort =>
        rootComponent (carrierRepresentative rootPort q))} :=
  (rootPortDebtSlotEquivCarrierCollision F rootPort).toEmbedding.trans
    { toFun := fun duplicate => ⟨rootComponent duplicate.1, by
        rintro ⟨q, hq⟩
        have hroot : duplicate.1 = carrierRepresentative rootPort q :=
          hcomponent hq.symm
        apply duplicate.2
        have hclass : carrierQuotientMk rootPort duplicate.1 = q := by
          rw [hroot, carrierQuotientMk_representative]
        rw [hclass]
        exact hroot⟩
      inj' := fun a b hab => by
        apply Subtype.ext
        exact hcomponent (congrArg Subtype.val hab) }

/-! ### Representative-per-port root quotients

The arbitrary representative used by `CarrierCollision` need not be the root
whose component has already been reserved elsewhere.  The following API makes
that choice explicit. -/

/-- One specified occurrence root to remove over each used physical port. -/
structure RootPortRepresentativeChoice where
  representative : CarrierQuotient rootPort → ↥F.roots
  representative_class : ∀ q,
    carrierQuotientMk rootPort (representative q) = q

/-- Roots left after removing the specified representative over each port. -/
def RootPortResidualRoot (choice : RootPortRepresentativeChoice F rootPort) :=
  {r : ↥F.roots // r ≠ choice.representative (carrierQuotientMk rootPort r)}

noncomputable instance rootPortResidualRootFintype
    (choice : RootPortRepresentativeChoice F rootPort) :
    Fintype (RootPortResidualRoot F rootPort choice) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The roots split into one prescribed representative per port and all
remaining occurrence-labelled roots. -/
noncomputable def rootPortRepresentativeResidualEquiv
    (choice : RootPortRepresentativeChoice F rootPort) :
    ↥F.roots ≃ CarrierQuotient rootPort ⊕ RootPortResidualRoot F rootPort choice := by
  classical
  refine
    { toFun := fun r =>
        if h : r = choice.representative (carrierQuotientMk rootPort r)
        then .inl (carrierQuotientMk rootPort r) else .inr ⟨r, h⟩
      invFun := fun x => match x with
        | .inl q => choice.representative q
        | .inr r => r.1
      left_inv := ?_
      right_inv := ?_ }
  · intro r
    by_cases h : r = choice.representative (carrierQuotientMk rootPort r)
    · dsimp
      rw [dif_pos h]
      exact h.symm
    · dsimp
      rw [dif_neg h]
  · intro x
    rcases x with q | r
    · have hclass := choice.representative_class q
      have hrep : choice.representative q =
          choice.representative
            (carrierQuotientMk rootPort (choice.representative q)) := by
        rw [hclass]
      dsimp
      rw [dif_pos hrep]
      exact congrArg Sum.inl hclass
    · dsimp
      rw [dif_neg r.2]
      exact congrArg Sum.inr (Subtype.ext rfl)

/-- Concrete debt slots are equivalent to the roots left by any choice of one
representative over each used port. -/
noncomputable def rootPortDebtSlotEquivResidualRoot
    (choice : RootPortRepresentativeChoice F rootPort) :
    F.RootPortDebtSlot rootPort ≃ RootPortResidualRoot F rootPort choice := by
  apply Fintype.equivOfCardEq
  have hroots := F.card_usedRootPorts_add_rootPortDebt rootPort
  have hsplit := Fintype.card_congr
    (rootPortRepresentativeResidualEquiv F rootPort choice)
  have hused : Fintype.card (CarrierQuotient rootPort) =
      (F.usedRootPorts rootPort).card := by
    rw [Fintype.card_congr
      (rootPortCarrierQuotientEquivUsedRootPorts F rootPort), Fintype.card_coe]
  rw [Fintype.card_sum, Fintype.card_coe] at hsplit
  rw [F.card_rootPortDebtSlot]
  omega

/-- The exact obstruction to choosing a prescribed reserved component over a
port: no root in that port fiber has the prescribed component. -/
def RootPortRepresentativeException {K : Type*}
    (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K) :=
  {q : CarrierQuotient rootPort // ∀ r : ↥F.roots,
    carrierQuotientMk rootPort r = q →
      rootComponent r ≠ reservedComponent q}

noncomputable instance rootPortRepresentativeExceptionFintype
    {K : Type*} (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K) :
    Fintype (RootPortRepresentativeException F rootPort rootComponent
      reservedComponent) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Fiberwise coverage is precisely absence of a representative exception. -/
theorem rootPortRepresentativeException_isEmpty_iff
    {K : Type*} (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K) :
    IsEmpty (RootPortRepresentativeException F rootPort rootComponent
      reservedComponent) ↔
      ∀ q, ∃ r : ↥F.roots, carrierQuotientMk rootPort r = q ∧
        rootComponent r = reservedComponent q := by
  classical
  constructor
  · intro hempty q
    by_contra h
    push_neg at h
    exact hempty.false ⟨q, h⟩
  · intro h
    refine ⟨fun exception => ?_⟩
    obtain ⟨r, hrclass, hrcomponent⟩ := h exception.1
    exact exception.2 r hrclass hrcomponent

/-- Active-root occurrences over the exceptional port.  This fiber is always
nonempty: the exception says that none of its members has the prescribed
component, not that the used port has no active root. -/
def RootPortRepresentativeProvenance
    {K : Type*} (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K)
    (exception : RootPortRepresentativeException F rootPort rootComponent
      reservedComponent) :=
  {r : ↥F.roots // carrierQuotientMk rootPort r = exception.1}

noncomputable def rootPortRepresentativeProvenanceCandidates
    {K : Type*} (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K)
    (exception : RootPortRepresentativeException F rootPort rootComponent
      reservedComponent) : Finset ↥F.roots :=
  Finset.univ.filter fun r =>
    rootPort r = carrierQuotientEmbedding rootPort exception.1

@[simp] theorem mem_rootPortRepresentativeProvenanceCandidates
    {K : Type*} (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K)
    (exception : RootPortRepresentativeException F rootPort rootComponent
      reservedComponent) (r : ↥F.roots) :
    r ∈ rootPortRepresentativeProvenanceCandidates F rootPort rootComponent
        reservedComponent exception ↔
      rootPort r = carrierQuotientEmbedding rootPort exception.1 := by
  classical
  simp [rootPortRepresentativeProvenanceCandidates]

/-- Every representative exception has at least one active-root provenance
candidate over its port. -/
theorem rootPortRepresentativeProvenanceCandidates_nonempty
    {K : Type*} (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K)
    (exception : RootPortRepresentativeException F rootPort rootComponent
      reservedComponent) :
    (rootPortRepresentativeProvenanceCandidates F rootPort rootComponent
      reservedComponent exception).Nonempty := by
  classical
  refine ⟨carrierRepresentative rootPort exception.1, ?_⟩
  rw [mem_rootPortRepresentativeProvenanceCandidates]
  have h := congrArg (carrierQuotientEmbedding rootPort)
    (carrierQuotientMk_representative rootPort exception.1)
  simpa only [carrierQuotientEmbedding_mk] using h

/-- Resources reachable from an exception through any active root over its
port.  The union retains root provenance instead of pretending that the absent
prescribed-component root exists. -/
noncomputable def rootPortRepresentativeExceptionNeighborhood
    {K R : Type*} [DecidableEq R]
    (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K)
    (candidates : ↥F.roots → Finset R)
    (exception : RootPortRepresentativeException F rootPort rootComponent
      reservedComponent) : Finset R :=
  (rootPortRepresentativeProvenanceCandidates F rootPort rootComponent
    reservedComponent exception).biUnion candidates

/-- Exact routing criterion for representative exceptions after expanding each
exception to the candidate resources of its active-root provenance fiber. -/
theorem rootPortRepresentativeExceptionHall_iff_nonempty_routing
    {K R : Type*} [DecidableEq R]
    (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K)
    (candidates : ↥F.roots → Finset R) :
    LocalizedHall (rootPortRepresentativeExceptionNeighborhood F rootPort
      rootComponent reservedComponent candidates) ↔
      Nonempty (LocalizedRouting
        (rootPortRepresentativeExceptionNeighborhood F rootPort
          rootComponent reservedComponent candidates)) :=
  localizedHall_iff_nonempty_routing _

/-- Choose the root carrying the prescribed reserved component in each port
fiber.  The coverage hypothesis is exactly the negation of the exception above. -/
noncomputable def rootPortRepresentativeChoiceOfComponent
    {K : Type*} (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K)
    (hcoverage : ∀ q, ∃ r : ↥F.roots,
      carrierQuotientMk rootPort r = q ∧
        rootComponent r = reservedComponent q) :
    RootPortRepresentativeChoice F rootPort where
  representative q := Classical.choose (hcoverage q)
  representative_class q := (Classical.choose_spec (hcoverage q)).1

@[simp] theorem rootPortRepresentativeChoiceOfComponent_component
    {K : Type*} (rootComponent : ↥F.roots → K)
    (reservedComponent : CarrierQuotient rootPort → K)
    (hcoverage : ∀ q, ∃ r : ↥F.roots,
      carrierQuotientMk rootPort r = q ∧
        rootComponent r = reservedComponent q) (q) :
    rootComponent ((rootPortRepresentativeChoiceOfComponent F rootPort
      rootComponent reservedComponent hcoverage).representative q) =
        reservedComponent q :=
  (Classical.choose_spec (hcoverage q)).2

/-- Once the representative carrying the prescribed reserved component is the
one removed over every port, every duplicate root component is residual. -/
noncomputable def rootPortDebtSlotResidualComponentEmbedding
    {K : Type*} (rootComponent : ↥F.roots → K)
    (hcomponent : Function.Injective rootComponent)
    (reservedComponent : CarrierQuotient rootPort → K)
    (hcoverage : ∀ q, ∃ r : ↥F.roots,
      carrierQuotientMk rootPort r = q ∧
        rootComponent r = reservedComponent q) :
    F.RootPortDebtSlot rootPort ↪
      {k : K // k ∉ Set.range reservedComponent} := by
  let choice := rootPortRepresentativeChoiceOfComponent F rootPort
    rootComponent reservedComponent hcoverage
  exact (rootPortDebtSlotEquivResidualRoot F rootPort choice).toEmbedding.trans
    { toFun := fun duplicate => ⟨rootComponent duplicate.1, by
        rintro ⟨q, hq⟩
        have hrepComponent : rootComponent (choice.representative q) =
            reservedComponent q :=
          rootPortRepresentativeChoiceOfComponent_component F rootPort
            rootComponent reservedComponent hcoverage q
        have hroot : duplicate.1 = choice.representative q :=
          hcomponent (hq.symm.trans hrepComponent.symm)
        apply duplicate.2
        have hclass : carrierQuotientMk rootPort duplicate.1 = q := by
          rw [hroot, choice.representative_class]
        rw [hclass]
        exact hroot⟩
      inj' := fun a b hab => by
        apply Subtype.ext
        exact hcomponent (congrArg Subtype.val hab) }

end RootPortMultiplicity

variable {M : Type w} {I : Type*}

/-- Accounting data after reserving the canonical carrier image of every
quotient class.  Merger slots and extra occurrences may use internal resources
or only components outside those reserved images. -/
structure TerminalCarrierQuotientRouting (carrier : A -> K) (M : Type w) (I : Type*) where
  complementaryEmbedding :
    (M ⊕ CarrierCollision carrier) ↪
      (I ⊕ {k : K // k ∉ Set.range (carrierQuotientEmbedding carrier)})

private def complementaryResourceEmbedding {carrier : A -> K} :
    (I ⊕ {k : K // k ∉ Set.range (carrierQuotientEmbedding carrier)}) ↪ (I ⊕ K) where
  toFun
    | Sum.inl i => Sum.inl i
    | Sum.inr k => Sum.inr k.1
  inj' := by
    intro x y h
    rcases x with i | k <;> rcases y with j | l
    · exact congrArg Sum.inl (Sum.inl.inj h)
    · simp at h
    · simp at h
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

private def reservedCarrierResourceEmbedding
    {carrier : A -> K} (R : TerminalCarrierQuotientRouting carrier M I) :
    (CarrierQuotient carrier ⊕ (M ⊕ CarrierCollision carrier)) ↪ (I ⊕ K) where
  toFun
    | Sum.inl q => Sum.inr (carrierQuotientEmbedding carrier q)
    | Sum.inr x => complementaryResourceEmbedding (carrier := carrier)
        (R.complementaryEmbedding x)
  inj' := by
    intro x y h
    rcases x with q | x <;> rcases y with r | y
    · exact congrArg Sum.inl ((carrierQuotientEmbedding carrier).injective (Sum.inr.inj h))
    · rcases hxy : R.complementaryEmbedding y with i | k
      · simp [complementaryResourceEmbedding, hxy] at h
      · have heq : carrierQuotientEmbedding carrier q = k.1 := by
          change Sum.inr (carrierQuotientEmbedding carrier q) =
            complementaryResourceEmbedding (R.complementaryEmbedding y) at h
          rw [hxy] at h
          exact Sum.inr.inj h
        exact (k.2 ⟨q, heq⟩).elim
    · rcases hxx : R.complementaryEmbedding x with i | k
      · simp [complementaryResourceEmbedding, hxx] at h
      · have heq : k.1 = carrierQuotientEmbedding carrier r := by
          change complementaryResourceEmbedding (R.complementaryEmbedding x) =
            Sum.inr (carrierQuotientEmbedding carrier r) at h
          rw [hxx] at h
          exact Sum.inr.inj h
        exact (k.2 ⟨r, heq.symm⟩).elim
    · apply congrArg Sum.inr
      apply R.complementaryEmbedding.injective
      apply (complementaryResourceEmbedding (carrier := carrier)).injective
      exact h

private noncomputable def mergerOccurrenceEquiv (carrier : A -> K) :
    (M ⊕ A) ≃ (CarrierQuotient carrier ⊕ (M ⊕ CarrierCollision carrier)) :=
  (Equiv.sumCongr (Equiv.refl M) (carrierQuotientCollisionEquiv carrier)).trans <|
    ((Equiv.sumAssoc M (CarrierQuotient carrier) (CarrierCollision carrier)).symm.trans <|
      (Equiv.sumCongr
        (Equiv.sumComm M (CarrierQuotient carrier))
        (Equiv.refl (CarrierCollision carrier))).trans <|
          Equiv.sumAssoc (CarrierQuotient carrier) M (CarrierCollision carrier))

/-- Recover the old raw terminal embedding from quotient-class accounting. -/
noncomputable def TerminalCarrierQuotientRouting.rawTerminalEmbedding
    {carrier : A -> K} (R : TerminalCarrierQuotientRouting carrier M I) :
    (M ⊕ A) ↪ (I ⊕ K) :=
  (mergerOccurrenceEquiv carrier).toEmbedding.trans
    (reservedCarrierResourceEmbedding R)

section PhysicalTreeTokens

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

/-- Tree-edge tokens whose physical edge is internal to the cotree support. -/
def InternalTreeEdgeToken (U : Finset (GridVertex m n))
    (tokenEdge : A ↪ ↥T.edgeFinset) :=
  {a : A // TreeEdgeTokenIsInternal U tokenEdge a}

noncomputable instance internalTreeEdgeTokenFintype [Fintype A]
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset) :
    Fintype (InternalTreeEdgeToken U tokenEdge) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance noninternalTreeEdgeTokenFintype [Fintype A]
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset) :
    Fintype (NoninternalTreeEdgeToken U tokenEdge) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The canonical internal resource reserved by an internal tree-edge token. -/
def internalTreeEdgeTokenEmbedding (U : Finset (GridVertex m n))
    (tokenEdge : A ↪ ↥T.edgeFinset) :
    InternalTreeEdgeToken U tokenEdge ↪ ↥(internalEdgeFinset T U) where
  toFun a := ⟨(tokenEdge a.1).1, by
    rw [mem_internalEdgeFinset]
    exact ⟨(tokenEdge a.1).2, a.2⟩⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply tokenEdge.injective
    apply Subtype.ext
    exact congrArg (fun e : ↥(internalEdgeFinset T U) => e.1) hab

/-- Every token is canonically classified as internal or noninternal. -/
noncomputable def treeEdgeTokenInternalNoninternalEquiv
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset) :
    A ≃ (InternalTreeEdgeToken U tokenEdge ⊕
      NoninternalTreeEdgeToken U tokenEdge) := by
  classical
  refine
    { toFun := fun a => if ha : TreeEdgeTokenIsInternal U tokenEdge a
        then Sum.inl ⟨a, ha⟩ else Sum.inr ⟨a, ha⟩
      invFun := fun x => match x with | .inl a => a.1 | .inr a => a.1
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    by_cases ha : TreeEdgeTokenIsInternal U tokenEdge a <;> simp [ha]
  · intro x
    rcases x with a | a
    · simp [a.2]
    · simp [a.2]

/-- The exact residual routing datum after physical tree-token resources are
reserved. Internal tokens reserve their own edges. One representative of each
noninternal component class reserves that component. Thus only the remaining
labelled collisions need routing, outside both reserved ranges. -/
structure PhysicalTreeTokenQuotientRouting
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset) where
  complementaryEmbedding :
    CarrierCollision (noninternalTreeEdgeTokenComponent U tokenEdge) ↪
      ({e : ↥(internalEdgeFinset T U) //
          e ∉ Set.range (internalTreeEdgeTokenEmbedding U tokenEdge)} ⊕
        {k : ((gridGraph m n).induce
            (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
              Set (GridVertex m n))).ConnectedComponent //
          k ∉ Set.range (carrierQuotientEmbedding
            (noninternalTreeEdgeTokenComponent U tokenEdge))})

noncomputable instance physicalTreeTokenCarrierCollisionFintype
    [Fintype A] (U : Finset (GridVertex m n))
    (tokenEdge : A ↪ ↥T.edgeFinset) :
    Fintype (CarrierCollision (noninternalTreeEdgeTokenComponent U tokenEdge)) := by
  classical
  exact Fintype.ofInjective (fun c => c.1.1) (by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab)

noncomputable instance unreservedInternalTreeEdgeFintype
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset) :
    Fintype {e : ↥(internalEdgeFinset T U) //
      e ∉ Set.range (internalTreeEdgeTokenEmbedding U tokenEdge)} := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance unreservedTreeTokenComponentFintype
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset) :
    Fintype {k : ((gridGraph m n).induce
        (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
          Set (GridVertex m n))).ConnectedComponent //
      k ∉ Set.range (carrierQuotientEmbedding
        (noninternalTreeEdgeTokenComponent U tokenEdge))} := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Existence of residual physical-token routing is exactly the finite capacity
inequality for labelled carrier collisions after all canonical reservations. -/
theorem nonempty_physicalTreeTokenQuotientRouting_iff_card_le
    [Fintype A] [DecidableEq A]
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset) :
    Nonempty (PhysicalTreeTokenQuotientRouting U tokenEdge) ↔
      Fintype.card
          (CarrierCollision (noninternalTreeEdgeTokenComponent U tokenEdge)) ≤
        Fintype.card
            {e : ↥(internalEdgeFinset T U) //
              e ∉ Set.range (internalTreeEdgeTokenEmbedding U tokenEdge)} +
          Fintype.card
            {k : ((gridGraph m n).induce
                (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
                  Set (GridVertex m n))).ConnectedComponent //
              k ∉ Set.range (carrierQuotientEmbedding
                (noninternalTreeEdgeTokenComponent U tokenEdge))} := by
  classical
  constructor
  · rintro ⟨R⟩
    rw [← Fintype.card_sum]
    exact Fintype.card_le_of_injective
      R.complementaryEmbedding.toFun R.complementaryEmbedding.injective
  · intro h
    refine ⟨⟨Classical.choice ?_⟩⟩
    rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_sum]
    exact h

/-- Physical tree tokens factor through their internal edge or preserved
component once the exact residual collision routing is supplied. -/
noncomputable def PhysicalTreeTokenQuotientRouting.resourceEmbedding
    {U : Finset (GridVertex m n)} {tokenEdge : A ↪ ↥T.edgeFinset}
    (R : PhysicalTreeTokenQuotientRouting U tokenEdge) :
    A ↪ (↥(internalEdgeFinset T U) ⊕
      ((gridGraph m n).induce
        (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
          Set (GridVertex m n))).ConnectedComponent) := by
  classical
  let carrier := noninternalTreeEdgeTokenComponent U tokenEdge
  let splitNoninternal := carrierQuotientCollisionEquiv carrier
  let sourceEquiv := (treeEdgeTokenInternalNoninternalEquiv U tokenEdge).trans
    (Equiv.sumCongr (Equiv.refl _) splitNoninternal)
  refine sourceEquiv.toEmbedding.trans
    { toFun := fun x => match x with
        | .inl a => Sum.inl (internalTreeEdgeTokenEmbedding U tokenEdge a)
        | .inr (.inl q) => Sum.inr (carrierQuotientEmbedding carrier q)
        | .inr (.inr c) => match R.complementaryEmbedding c with
          | .inl e => Sum.inl e.1
          | .inr k => Sum.inr k.1
      inj' := ?_ }
  intro x y hxy
  rcases x with a | x <;> rcases y with b | y
  · exact congrArg Sum.inl ((internalTreeEdgeTokenEmbedding U tokenEdge).injective
      (Sum.inl.inj hxy))
  · rcases y with q | c
    · simp at hxy
    · rcases hc : R.complementaryEmbedding c with e | k
      · have heq : internalTreeEdgeTokenEmbedding U tokenEdge a = e.1 := by
          simpa [hc] using hxy
        exact (e.2 ⟨a, heq⟩).elim
      · simp [hc] at hxy
  · rcases x with q | c
    · simp at hxy
    · rcases hc : R.complementaryEmbedding c with e | k
      · have heq : e.1 = internalTreeEdgeTokenEmbedding U tokenEdge b := by
          simpa [hc] using hxy
        exact (e.2 ⟨b, heq.symm⟩).elim
      · simp [hc] at hxy
  · rcases x with q | c <;> rcases y with r | d
    · exact congrArg (fun z => Sum.inr (Sum.inl z))
        ((carrierQuotientEmbedding carrier).injective (Sum.inr.inj hxy))
    · rcases hd : R.complementaryEmbedding d with e | k
      · simp [hd] at hxy
      · have heq : carrierQuotientEmbedding carrier q = k.1 := by
          simpa [hd] using hxy
        exact (k.2 ⟨q, heq⟩).elim
    · rcases hc : R.complementaryEmbedding c with e | k
      · simp [hc] at hxy
      · have heq : k.1 = carrierQuotientEmbedding carrier r := by
          simpa [hc] using hxy
        exact (k.2 ⟨r, heq.symm⟩).elim
    · apply congrArg (fun z => Sum.inr (Sum.inr z))
      apply R.complementaryEmbedding.injective
      rcases hc : R.complementaryEmbedding c with e | k <;>
        rcases hd : R.complementaryEmbedding d with f | l <;>
        simp [hc, hd] at hxy ⊢
      · exact Subtype.ext hxy
      · exact Subtype.ext hxy

/-- Residual routing after ports and the canonical physical tree-token
resources are reserved. -/
structure PortAwarePhysicalTreeTokenQuotientRouting
    {P0 P : Type*} (port : P0 ↪ P)
    (U : Finset (GridVertex m n)) (tokenEdge : A ↪ ↥T.edgeFinset) where
  complementaryEmbedding :
    CarrierCollision (noninternalTreeEdgeTokenComponent U tokenEdge) ↪
      ({p : P // p ∉ Set.range port} ⊕
        ({e : ↥(internalEdgeFinset T U) //
            e ∉ Set.range (internalTreeEdgeTokenEmbedding U tokenEdge)} ⊕
          {k : ((gridGraph m n).induce
              (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
                Set (GridVertex m n))).ConnectedComponent //
            k ∉ Set.range (carrierQuotientEmbedding
              (noninternalTreeEdgeTokenComponent U tokenEdge))}))

noncomputable instance unreservedPortFintype {P0 P : Type*} [Fintype P]
    (port : P0 ↪ P) : Fintype {p : P // p ∉ Set.range port} := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Port-aware residual routing exists exactly when the three unreserved pools
have enough finite capacity for the labelled carrier collisions. -/
theorem nonempty_portAwarePhysicalTreeTokenQuotientRouting_iff_card_le
    {P0 P : Type*} [Fintype P] [Fintype A] [DecidableEq A]
    (port : P0 ↪ P) (U : Finset (GridVertex m n))
    (tokenEdge : A ↪ ↥T.edgeFinset) :
    Nonempty (PortAwarePhysicalTreeTokenQuotientRouting port U tokenEdge) ↔
      Fintype.card
          (CarrierCollision (noninternalTreeEdgeTokenComponent U tokenEdge)) ≤
        Fintype.card {p : P // p ∉ Set.range port} +
          (Fintype.card
              {e : ↥(internalEdgeFinset T U) //
                e ∉ Set.range (internalTreeEdgeTokenEmbedding U tokenEdge)} +
            Fintype.card
              {k : ((gridGraph m n).induce
                  (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
                    Set (GridVertex m n))).ConnectedComponent //
                k ∉ Set.range (carrierQuotientEmbedding
                  (noninternalTreeEdgeTokenComponent U tokenEdge))}) := by
  classical
  constructor
  · rintro ⟨R⟩
    rw [← Fintype.card_sum, ← Fintype.card_sum]
    exact Fintype.card_le_of_injective
      R.complementaryEmbedding.toFun R.complementaryEmbedding.injective
  · intro h
    refine ⟨⟨Classical.choice ?_⟩⟩
    rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_sum,
      Fintype.card_sum]
    exact h

/-- An embedding range and its complement partition a finite target exactly. -/
private theorem card_add_card_not_range_eq
    {X Y : Type*} [Fintype X] [Fintype Y] (e : X ↪ Y) :
    Fintype.card X + Fintype.card {y : Y // y ∉ Set.range e} =
      Fintype.card Y := by
  classical
  have hrange : Fintype.card X =
      Fintype.card {y : Y // y ∈ Set.range e} :=
    Fintype.card_congr e.toEquivRange
  have hcompl := Fintype.card_subtype_compl (fun y : Y => y ∈ Set.range e)
  have hle : Fintype.card X ≤ Fintype.card Y :=
    Fintype.card_le_of_injective e e.injective
  rw [← hrange] at hcompl
  omega

/-- Exact total-capacity audit for port-aware physical-token routing when every
token is noninternal.  This is obtained from the quotient/collision partition
and the three reservation/complement partitions; it is not an assumed capacity
inequality. -/
theorem nonempty_portAwarePhysicalTreeTokenQuotientRouting_iff_total_card_le
    {P0 P : Type*} [Fintype P0] [Fintype P] [Fintype A] [DecidableEq A]
    (port : P0 ↪ P) (U : Finset (GridVertex m n))
    (tokenEdge : A ↪ ↥T.edgeFinset)
    (hnoninternal : ∀ a, ¬TreeEdgeTokenIsInternal U tokenEdge a) :
    Nonempty (PortAwarePhysicalTreeTokenQuotientRouting port U tokenEdge) ↔
      Fintype.card P0 + Fintype.card A ≤
        Fintype.card P + (internalEdgeFinset T U).card +
          Fintype.card ((gridGraph m n).induce
            (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
              Set (GridVertex m n))).ConnectedComponent := by
  classical
  let carrier := noninternalTreeEdgeTokenComponent U tokenEdge
  have hinternal : Fintype.card (InternalTreeEdgeToken U tokenEdge) = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun a => (hnoninternal a.1 a.2).elim⟩
  have htokenPartition : Fintype.card A =
      Fintype.card (InternalTreeEdgeToken U tokenEdge) +
        Fintype.card (NoninternalTreeEdgeToken U tokenEdge) := by
    rw [Fintype.card_congr
      (treeEdgeTokenInternalNoninternalEquiv U tokenEdge), Fintype.card_sum]
  have hcollisionPartition :
      Fintype.card (NoninternalTreeEdgeToken U tokenEdge) =
        Fintype.card (CarrierQuotient carrier) +
          Fintype.card (CarrierCollision carrier) :=
    by
      rw [Fintype.card_congr (carrierQuotientCollisionEquiv carrier),
        Fintype.card_sum]
  have hportPartition := card_add_card_not_range_eq port
  have hinternalPartition :=
    card_add_card_not_range_eq (internalTreeEdgeTokenEmbedding U tokenEdge)
  have hcomponentPartition :=
    card_add_card_not_range_eq (carrierQuotientEmbedding carrier)
  rw [nonempty_portAwarePhysicalTreeTokenQuotientRouting_iff_card_le]
  dsimp only [carrier] at hcollisionPartition hcomponentPartition ⊢
  simp only [Fintype.card_coe] at hinternalPartition ⊢
  omega

/-- Ports, internal tokens, and one representative of each noninternal
component class occupy their reserved physical resources; labelled collisions
use only the complement of all three reservations. -/
noncomputable def PortAwarePhysicalTreeTokenQuotientRouting.resourceEmbedding
    {P0 P : Type*} {port : P0 ↪ P}
    {U : Finset (GridVertex m n)} {tokenEdge : A ↪ ↥T.edgeFinset}
    (R : PortAwarePhysicalTreeTokenQuotientRouting port U tokenEdge) :
    (P0 ⊕ A) ↪ (P ⊕ (↥(internalEdgeFinset T U) ⊕
      ((gridGraph m n).induce
        (↑((Finset.univ : Finset (GridVertex m n)) \ U) :
          Set (GridVertex m n))).ConnectedComponent)) := by
  classical
  let carrier := noninternalTreeEdgeTokenComponent U tokenEdge
  let splitNoninternal := carrierQuotientCollisionEquiv carrier
  let tokenEquiv := (treeEdgeTokenInternalNoninternalEquiv U tokenEdge).trans
    (Equiv.sumCongr (Equiv.refl _) splitNoninternal)
  let sourceEquiv := Equiv.sumCongr (Equiv.refl P0) tokenEquiv
  refine sourceEquiv.toEmbedding.trans
    { toFun := fun x => match x with
        | .inl p => Sum.inl (port p)
        | .inr (.inl a) => Sum.inr (Sum.inl
            (internalTreeEdgeTokenEmbedding U tokenEdge a))
        | .inr (.inr (.inl q)) => Sum.inr (Sum.inr
            (carrierQuotientEmbedding carrier q))
        | .inr (.inr (.inr c)) => match R.complementaryEmbedding c with
          | .inl p => Sum.inl p.1
          | .inr (.inl e) => Sum.inr (Sum.inl e.1)
          | .inr (.inr k) => Sum.inr (Sum.inr k.1)
      inj' := ?_ }
  intro x y hxy
  rcases x with p | x <;> rcases y with q | y
  · exact congrArg Sum.inl (port.injective (Sum.inl.inj hxy))
  · rcases y with a | y
    · simp at hxy
    · rcases y with r | c
      · simp at hxy
      · rcases hc : R.complementaryEmbedding c with s | z
        · have heq : port p = s.1 := by simpa [hc] using hxy
          exact (s.2 ⟨p, heq⟩).elim
        · rcases z with e | k <;> simp [hc] at hxy
  · rcases x with a | x
    · simp at hxy
    · rcases x with r | c
      · simp at hxy
      · rcases hc : R.complementaryEmbedding c with s | z
        · have heq : s.1 = port q := by simpa [hc] using hxy
          exact (s.2 ⟨q, heq.symm⟩).elim
        · rcases z with e | k <;> simp [hc] at hxy
  · rcases x with a | x <;> rcases y with b | y
    · exact congrArg (fun z => Sum.inr (Sum.inl z))
        ((internalTreeEdgeTokenEmbedding U tokenEdge).injective
          (Sum.inl.inj (Sum.inr.inj hxy)))
    · rcases y with q | c
      · simp at hxy
      · rcases hc : R.complementaryEmbedding c with p | z
        · simp [hc] at hxy
        · rcases z with e | k
          · have heq : internalTreeEdgeTokenEmbedding U tokenEdge a = e.1 := by
              simpa [hc] using hxy
            exact (e.2 ⟨a, heq⟩).elim
          · simp [hc] at hxy
    · rcases x with q | c
      · simp at hxy
      · rcases hc : R.complementaryEmbedding c with p | z
        · simp [hc] at hxy
        · rcases z with e | k
          · have heq : e.1 = internalTreeEdgeTokenEmbedding U tokenEdge b := by
              simpa [hc] using hxy
            exact (e.2 ⟨b, heq.symm⟩).elim
          · simp [hc] at hxy
    · rcases x with q | c <;> rcases y with r | d
      · exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inl z)))
          ((carrierQuotientEmbedding carrier).injective
            (Sum.inr.inj (Sum.inr.inj hxy)))
      · rcases hd : R.complementaryEmbedding d with p | z
        · simp [hd] at hxy
        · rcases z with e | k
          · simp [hd] at hxy
          · have heq : carrierQuotientEmbedding carrier q = k.1 := by
              simpa [hd] using hxy
            exact (k.2 ⟨q, heq⟩).elim
      · rcases hc : R.complementaryEmbedding c with p | z
        · simp [hc] at hxy
        · rcases z with e | k
          · simp [hc] at hxy
          · have heq : k.1 = carrierQuotientEmbedding carrier r := by
              simpa [hc] using hxy
            exact (k.2 ⟨r, heq.symm⟩).elim
      · apply congrArg (fun z => Sum.inr (Sum.inr (Sum.inr z)))
        apply R.complementaryEmbedding.injective
        rcases hc : R.complementaryEmbedding c with p | z <;>
          rcases hd : R.complementaryEmbedding d with q | w
        · exact congrArg Sum.inl (Subtype.ext (by simpa [hc, hd] using hxy))
        · rcases w with f | l <;> simp [hc, hd] at hxy
        · rcases z with e | k <;> simp [hc, hd] at hxy
        · rcases z with e | k <;> rcases w with f | l
          · exact congrArg (fun t => Sum.inr (Sum.inl t))
              (Subtype.ext (by simpa [hc, hd] using hxy))
          · simp [hc, hd] at hxy
          · simp [hc, hd] at hxy
          · exact congrArg (fun t => Sum.inr (Sum.inr t))
              (Subtype.ext (by simpa [hc, hd] using hxy))

end PhysicalTreeTokens

namespace ParentForest

variable {V X : Type*} [Fintype V] [DecidableEq V]
variable [Fintype X] [DecidableEq X]

/-- Component carrier of a root surviving removal of the later exits. -/
def survivingRootCarrier (F : ParentForest V) (G : SimpleGraph X) (U : Finset X)
    (exits : Finset V)
    (rootContact : ↥(F.roots \ exits) -> ↥(CotreeFreeSet U)) :
    ↥(F.roots \ exits) -> (CotreeFreeGraph G U).ConnectedComponent :=
  fun r => (CotreeFreeGraph G U).connectedComponentMk (rootContact r)

/-- Carrier collisions among roots which survive later-exit pruning. -/
abbrev SurvivingRootCarrierCollision (F : ParentForest V) (G : SimpleGraph X)
    (U : Finset X) (exits : Finset V)
    (rootContact : ↥(F.roots \ exits) -> ↥(CotreeFreeSet U)) :=
  CarrierCollision (F.survivingRootCarrier G U exits rootContact)

/-- Quotient accounting specialized to surviving channel-forest roots. This
generic API requires an explicit cotree contact for every surviving root; it
does not derive contacts from physical tree edges. -/
abbrev SurvivingRootCarrierQuotientRouting (F : ParentForest V)
    (G : SimpleGraph X) (U : Finset X) (exits : Finset V)
    (rootContact : ↥(F.roots \ exits) -> ↥(CotreeFreeSet U)) (I : Type*) :=
  TerminalCarrierQuotientRouting (F.survivingRootCarrier G U exits rootContact)
    F.MergerSlot I

/-- Raw merger/surviving-root embedding supplied by quotient accounting. -/
noncomputable def SurvivingRootCarrierQuotientRouting.terminalEmbedding
    {F : ParentForest V} {G : SimpleGraph X} {U : Finset X} {exits : Finset V}
    {rootContact : ↥(F.roots \ exits) -> ↥(CotreeFreeSet U)} {I : Type*}
    (R : F.SurvivingRootCarrierQuotientRouting G U exits rootContact I) :
    (F.MergerSlot ⊕ ↥(F.roots \ exits)) ↪
      (I ⊕ (CotreeFreeGraph G U).ConnectedComponent) :=
  R.rawTerminalEmbedding

end ParentForest

namespace PlaneChannelForest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The carrier-quotient accounting hypotheses imply the corrected direct- and
later-exit contour bound.  Existence of the routing remains an explicit input. -/
theorem incidenceWaste_ge_of_terminalCarrierQuotientRoutingWithDirectExits
    {n : Nat} (hn : 2 <= n) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (C : PlaneChannelForest V)
    (directExits : Finset (CanonicalShoreDemand axis n))
    (continuingEmbedding :
      ↥((Finset.univ : Finset (CanonicalShoreDemand axis n)) \ directExits) ↪
        ↥C.demand)
    (hdemand : C.demand ⊆ C.forest.leaves)
    (hexits : C.exits ⊆ C.forest.roots)
    (exitEmbedding : (↥directExits ⊕ ↥C.exits) ↪
      BoundarySector (supportFinset (gridGraph n n \ T)))
    (rootContact : ↥(C.forest.roots \ C.exits) ->
      ↥(CotreeFreeSet (supportFinset (gridGraph n n \ T))))
    (routing : C.forest.SurvivingRootCarrierQuotientRouting
      (gridGraph n n) (supportFinset (gridGraph n n \ T)) C.exits rootContact
      ↥(internalEdgeFinset T (supportFinset (gridGraph n n \ T)))) :
    n + 2 <= incidenceWaste (gridGraph n n \ T) := by
  apply incidenceWaste_ge_of_prunedRootChannelRoutingWithDirectExits
    hn axis hT C directExits continuingEmbedding hdemand hexits exitEmbedding
  simpa [CotreeFreeGraph, CotreeFreeSet] using routing.terminalEmbedding

/-- A physical tree-edge label for every merger or surviving root reduces the
terminal obligation to routing only repeated contacts with the same preserved
component. Internal tokens and one representative of each component class are
reserved canonically by `PhysicalTreeTokenQuotientRouting`. -/
theorem incidenceWaste_ge_of_physicalTreeTokenQuotientRoutingWithDirectExits
    {n : Nat} (hn : 2 ≤ n) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (C : PlaneChannelForest V)
    (directExits : Finset (CanonicalShoreDemand axis n))
    (continuingEmbedding :
      ↥((Finset.univ : Finset (CanonicalShoreDemand axis n)) \ directExits) ↪
        ↥C.demand)
    (hdemand : C.demand ⊆ C.forest.leaves)
    (hexits : C.exits ⊆ C.forest.roots)
    (exitEmbedding : (↥directExits ⊕ ↥C.exits) ↪
      BoundarySector (supportFinset (gridGraph n n \ T)))
    (tokenEdge : (C.forest.MergerSlot ⊕ ↥(C.forest.roots \ C.exits)) ↪
      ↥T.edgeFinset)
    (routing : PhysicalTreeTokenQuotientRouting
      (supportFinset (gridGraph n n \ T)) tokenEdge) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) := by
  apply incidenceWaste_ge_of_prunedRootChannelRoutingWithDirectExits
    hn axis hT C directExits continuingEmbedding hdemand hexits exitEmbedding
  exact routing.resourceEmbedding

end PlaneChannelForest

end GridGraphs
