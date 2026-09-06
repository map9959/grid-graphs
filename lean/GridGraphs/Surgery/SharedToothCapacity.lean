import GridGraphs.Surgery.BundleToothCut
import GridGraphs.Forests.RootedForestCuts

/-!
# Shared tooth capacity

Repeated first endpoints save deletions only after the demands have been
counted with their labels.  This file records that finite-fiber accounting and
applies it to owner-labelled bundle-tooth demands.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {α β V O M : Type*}

/-- The number of demands in `S` whose first endpoint is `y`. -/
def endpointMultiplicity [DecidableEq β]
    (S : Finset α) (f : α → β) (y : β) : Nat :=
  (S.filter fun x => f x = y).card

/-- The deletion saved by grouping demands with the same first endpoint. -/
def endpointSaving [DecidableEq β] (S : Finset α) (f : α → β) : Nat :=
  ∑ y ∈ S.image f, (endpointMultiplicity S f y - 1)

/-- Exact finite first-endpoint fiber accounting. -/
theorem card_image_add_endpointSaving [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    (S.image f).card + endpointSaving S f = S.card := by
  have hsum : S.card = ∑ y ∈ S.image f, endpointMultiplicity S f y := by
    simpa only [endpointMultiplicity] using Finset.card_eq_sum_card_image f S
  have hpositive : ∀ y ∈ S.image f, 1 ≤ endpointMultiplicity S f y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    change 0 < (S.filter fun z => f z = f x).card
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  have hsplit :
      (∑ y ∈ S.image f, endpointMultiplicity S f y) =
        (S.image f).card + endpointSaving S f := by
    calc
      _ = ∑ y ∈ S.image f, (1 + (endpointMultiplicity S f y - 1)) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (Nat.add_sub_of_le (hpositive y hy)).symm
      _ = (∑ _y ∈ S.image f, 1) +
          ∑ y ∈ S.image f, (endpointMultiplicity S f y - 1) :=
        Finset.sum_add_distrib
      _ = _ := by rw [← Finset.card_eq_sum_ones]; rfl
  exact hsplit.symm.trans hsum.symm

/-- Grouping by first endpoint preserves an arbitrary additive weight. -/
theorem sum_endpointFibers [DecidableEq α] [DecidableEq β] [AddCommMonoid M]
    (S : Finset α) (f : α → β) (w : α → M) :
    (∑ x ∈ S, w x) =
      ∑ y ∈ S.image f, ∑ x ∈ S with f x = y, w x := by
  exact (Finset.sum_fiberwise_of_maps_to
    (s := S) (t := S.image f) (g := f)
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) w).symm

section CertificateFamily

variable [Fintype V]

/-- Owner-labelled terminal demands.  The sigma label keeps equal terminal
vertices belonging to different owners distinct. -/
noncomputable def ownerTerminalDemands (G : SimpleGraph V) (F : Set V) (u : O → V)
    (owners : Finset O) (C : ∀ o, BundleToothCertificate G F (u o)) :
    Finset (Σ _o : O, V) :=
  owners.sigma fun o => (C o).terminals

/-- The first endpoint attached to an owner-labelled terminal demand. -/
noncomputable def ownerTerminalEndpoint (G : SimpleGraph V) (F : Set V) (u : O → V)
    (C : ∀ o, BundleToothCertificate G F (u o)) : (Σ _o : O, V) → V :=
  fun d => (C d.1).endpoint d.2

/-- The physical deletion obtained by sharing equal first endpoints. -/
noncomputable def sharedEndpointDeletion [DecidableEq V]
    (G : SimpleGraph V) (F : Set V) (u : O → V)
    (owners : Finset O) (C : ∀ o, BundleToothCertificate G F (u o)) : Finset V :=
  (ownerTerminalDemands G F u owners C).image (ownerTerminalEndpoint G F u C)

/-- Owner labels make the demand count the sum of the per-owner defects. -/
theorem ownerTerminalDemands_card (G : SimpleGraph V) (F : Set V) (u : O → V)
    (owners : Finset O) (C : ∀ o, BundleToothCertificate G F (u o)) :
    (ownerTerminalDemands G F u owners C).card =
      ∑ o ∈ owners, bundleCycleDefect G F (u o) := by
  classical
  rw [ownerTerminalDemands, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro o ho
  exact (C o).terminals_card

/-- Exact shared-deletion capacity for a finite certificate family. -/
theorem sharedEndpointDeletion_card_add_saving
    [DecidableEq V]
    (G : SimpleGraph V) (F : Set V) (u : O → V)
    (owners : Finset O) (C : ∀ o, BundleToothCertificate G F (u o)) :
    (sharedEndpointDeletion G F u owners C).card +
        endpointSaving (ownerTerminalDemands G F u owners C)
          (ownerTerminalEndpoint G F u C) =
      ∑ o ∈ owners, bundleCycleDefect G F (u o) := by
  classical
  calc
    _ = (ownerTerminalDemands G F u owners C).card := by
      unfold sharedEndpointDeletion
      exact card_image_add_endpointSaving
        (ownerTerminalDemands G F u owners C) (ownerTerminalEndpoint G F u C)
    _ = _ := ownerTerminalDemands_card G F u owners C

/-- Simultaneous use of the shared endpoint deletion is sound when every shared
endpoint avoids every selected owner's neighbor set.  Coverage of each selected
certificate deletion follows from endpoint completeness. -/
theorem forcedInsertionCondition_after_sharedEndpointDeletion
    [DecidableEq V]
    (G : SimpleGraph V) (F : Set V) (u : O → V)
    (owners : Finset O) (C : ∀ o, BundleToothCertificate G F (u o))
    (hcompat : ∀ d ∈ sharedEndpointDeletion G F u owners C,
      ∀ o ∈ owners, d ∉ G.neighborSet (u o)) :
    ∀ o ∈ owners, ForcedInsertionCondition G
      (F \ (↑(sharedEndpointDeletion G F u owners C) : Set V)) (u o) := by
  classical
  intro o ho
  let D := sharedEndpointDeletion G F u owners C
  have hcoverage : (↑(C o).deletion : Set V) ⊆ (↑D : Set V) := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := (C o).deletion_covered_by_endpoints d hd
    apply Finset.mem_image.mpr
    refine ⟨⟨o, x⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨ho, hx⟩
  have hsmall : F \ (↑D : Set V) ⊆ F \ (↑(C o).deletion : Set V) := by
    intro x hx
    exact ⟨hx.1, fun hxD => hx.2 (hcoverage hxD)⟩
  have hattachment :
      ({u o} ∪ (G.neighborSet (u o) \ (F \ (↑D : Set V))) : Set V) =
        ({u o} ∪
          (G.neighborSet (u o) \ (F \ (↑(C o).deletion : Set V))) : Set V) := by
    ext x
    constructor
    · rintro (rfl | ⟨hxN, hxnot⟩)
      · exact Or.inl rfl
      · apply Or.inr
        refine ⟨hxN, ?_⟩
        rintro ⟨hxF, hxnotDelete⟩
        apply hxnot
        refine ⟨hxF, ?_⟩
        intro hxD
        exact hcompat x hxD o ho hxN
    · rintro (rfl | ⟨hxN, hxnot⟩)
      · exact Or.inl rfl
      · apply Or.inr
        refine ⟨hxN, ?_⟩
        rintro ⟨hxF, hxnotD⟩
        apply hxnot
        refine ⟨hxF, ?_⟩
        intro hxDelete
        exact Set.disjoint_left.mp (C o).deletion_disjoint_owner hxDelete hxN
  intro v hv w hw hvw hreach
  apply (C o).insertion (hattachment ▸ hv) (hattachment ▸ hw) hvw
  exact hreach.mono (forcedEdgeGraph_mono G hsmall)

end CertificateFamily

end GridGraphs
