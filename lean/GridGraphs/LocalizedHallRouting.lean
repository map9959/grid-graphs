import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Localized Hall routing

Finite demands can be routed injectively to resources when every finite set of
demands has a large enough combined neighborhood.  A specialization records
the common case where demands and resources are partitioned by an owner.
-/

namespace GridGraphs

open Finset
open scoped BigOperators

/-- Hall's condition for a finite-set-valued neighborhood. -/
def LocalizedHall {C R : Type*} [DecidableEq R] (N : C → Finset R) : Prop :=
  ∀ S : Finset C, S.card ≤ (S.biUnion N).card

/-- Hall inequalities may be proved one owner fiber at a time when candidate
neighborhoods belonging to distinct owners are disjoint.  This is a direct
cardinality argument; it does not extract a matching. -/
theorem localizedHall_of_fiberwise_of_neighborhood_disjoint
    {C R O : Type*} [DecidableEq C] [DecidableEq R] [DecidableEq O]
    (owner : C → O) (N : C → Finset R)
    (hfiber : ∀ o (S : Finset C),
      (∀ c ∈ S, owner c = o) → S.card ≤ (S.biUnion N).card)
    (hdisjoint : ∀ {c d}, owner c ≠ owner d → Disjoint (N c) (N d)) :
    LocalizedHall N := by
  intro S
  let owners := S.image owner
  let fiber := fun o => S.filter fun c => owner c = o
  let resources := fun o => (fiber o).biUnion N
  have hresources : S.biUnion N = owners.biUnion resources := by
    ext r
    dsimp only [owners, resources, fiber]
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨c, hcS, hr⟩
      exact ⟨owner c, ⟨c, hcS, rfl⟩, c, ⟨hcS, rfl⟩, hr⟩
    · rintro ⟨o, ⟨c, hcS, hco⟩, d, ⟨hdS, hdo⟩, hr⟩
      exact ⟨d, hdS, hr⟩
  have hpairwise : ∀ a ∈ owners, ∀ b ∈ owners, a ≠ b →
      Disjoint (resources a) (resources b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro r hra hrb
    dsimp only [resources, fiber] at hra hrb
    obtain ⟨c, hc, hrc⟩ := Finset.mem_biUnion.mp hra
    obtain ⟨d, hd, hrd⟩ := Finset.mem_biUnion.mp hrb
    obtain ⟨_hcS, hca⟩ := Finset.mem_filter.mp hc
    obtain ⟨_hdS, hdb⟩ := Finset.mem_filter.mp hd
    have howner : owner c ≠ owner d := by
      intro heq
      apply hab
      rw [← hca, ← hdb, heq]
    exact (Finset.disjoint_left.mp (hdisjoint howner)) hrc hrd
  calc
    S.card = ∑ o ∈ owners, (fiber o).card :=
      Finset.card_eq_sum_card_image owner S
    _ ≤ ∑ o ∈ owners, (resources o).card := by
      apply Finset.sum_le_sum
      intro o ho
      apply hfiber o (fiber o)
      intro c hc
      exact (Finset.mem_filter.mp hc).2
    _ = (owners.biUnion resources).card :=
      (Finset.card_biUnion hpairwise).symm
    _ = (S.biUnion N).card := by rw [hresources]

/-- A nonempty neighborhood proves the Hall inequality for source sets of
cardinality at most one. -/
theorem card_le_biUnion_of_card_le_one_of_neighborhood_nonempty
    {C R : Type*} [DecidableEq C] [DecidableEq R]
    (N : C → Finset R) (hnonempty : ∀ c, (N c).Nonempty)
    (S : Finset C) (hcard : S.card ≤ 1) :
    S.card ≤ (S.biUnion N).card := by
  by_cases hS : S = ∅
  · simp [hS]
  · obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨r, hr⟩ := hnonempty c
    have hrUnion : r ∈ S.biUnion N := Finset.mem_biUnion.mpr ⟨c, hc, hr⟩
    have hpositive : 0 < (S.biUnion N).card := Finset.card_pos.mpr ⟨r, hrUnion⟩
    omega

/-- Once singleton neighborhoods are nonempty and different owner fibers have
disjoint neighborhoods, every Hall failure is already witnessed by at least
two demands in one owner fiber. -/
theorem exists_same_fiber_deficiency_of_not_localizedHall
    {C R O : Type*} [DecidableEq C] [DecidableEq R] [DecidableEq O]
    (owner : C → O) (N : C → Finset R)
    (hnonempty : ∀ c, (N c).Nonempty)
    (hdisjoint : ∀ {c d}, owner c ≠ owner d → Disjoint (N c) (N d))
    (hnot : ¬LocalizedHall N) :
    ∃ (o : O) (S : Finset C), 2 ≤ S.card ∧
      (∀ c ∈ S, owner c = o) ∧ (S.biUnion N).card < S.card := by
  classical
  by_contra hdeficient
  apply hnot
  apply localizedHall_of_fiberwise_of_neighborhood_disjoint owner N
  · intro o S hsame
    by_cases hsmall : S.card ≤ 1
    · exact card_le_biUnion_of_card_le_one_of_neighborhood_nonempty
        N hnonempty S hsmall
    · have hlarge : 2 ≤ S.card := by omega
      have hnlt : ¬(S.biUnion N).card < S.card := by
        intro hlt
        exact hdeficient ⟨o, S, hlarge, hsame, hlt⟩
      omega
  · exact hdisjoint

/-- An injective choice of one allowed resource for every demand. -/
structure LocalizedRouting {C R : Type*} [DecidableEq R] (N : C → Finset R) where
  toEmbedding : C ↪ R
  mem_neighborhood : ∀ c, toEmbedding c ∈ N c

instance {C R : Type*} [DecidableEq R] {N : C → Finset R} :
    CoeFun (LocalizedRouting N) fun _ => C → R :=
  ⟨fun routing => routing.toEmbedding⟩

/-- Two localized routings combine when every neighborhood from one source
class is disjoint from every neighborhood from the other class. -/
noncomputable def LocalizedRouting.sum {A B R : Type*} [DecidableEq R]
    {NA : A → Finset R} {NB : B → Finset R}
    (left : LocalizedRouting NA) (right : LocalizedRouting NB)
    (hdisjoint : ∀ a b, Disjoint (NA a) (NB b)) :
    LocalizedRouting (fun source : A ⊕ B => source.elim NA NB) where
  toEmbedding :=
    { toFun := fun source => source.elim left right
      inj' := by
        intro a b hab
        rcases a with a | a <;> rcases b with b | b
        · exact congrArg Sum.inl (left.toEmbedding.injective hab)
        · exact False.elim ((Finset.disjoint_left.mp (hdisjoint a b))
            (left.mem_neighborhood a) (by
              change left.toEmbedding a = right.toEmbedding b at hab
              rw [hab]
              exact right.mem_neighborhood b))
        · exact False.elim ((Finset.disjoint_left.mp (hdisjoint b a))
            (by
              change right.toEmbedding a = left.toEmbedding b at hab
              rw [hab]
              exact left.mem_neighborhood b)
            (right.mem_neighborhood a))
        · exact congrArg Sum.inr (right.toEmbedding.injective hab) }
  mem_neighborhood := by
    intro source
    rcases source with source | source
    · exact left.mem_neighborhood source
    · exact right.mem_neighborhood source

/-- Two localized routings also combine when their selected images, rather than
their entire candidate neighborhoods, are disjoint. This is the exact condition
needed after classwise Hall choices have already been made. -/
noncomputable def LocalizedRouting.sumOfSelectedNe
    {A B R : Type*} [DecidableEq R]
    {NA : A → Finset R} {NB : B → Finset R}
    (left : LocalizedRouting NA) (right : LocalizedRouting NB)
    (hne : ∀ a b, left a ≠ right b) :
    LocalizedRouting (fun source : A ⊕ B => source.elim NA NB) where
  toEmbedding :=
    { toFun := fun source => source.elim left right
      inj' := by
        intro a b hab
        rcases a with a | a <;> rcases b with b | b
        · exact congrArg Sum.inl (left.toEmbedding.injective hab)
        · exact False.elim (hne a b hab)
        · exact False.elim (hne b a hab.symm)
        · exact congrArg Sum.inr (right.toEmbedding.injective hab) }
  mem_neighborhood := by
    intro source
    rcases source with source | source
    · exact left.mem_neighborhood source
    · exact right.mem_neighborhood source

/-- Finite Hall's theorem, expressed as an embedding respecting the given
neighborhoods. -/
theorem localizedHall_iff_exists_embedding {C R : Type*} [Finite C]
    [DecidableEq R] (N : C → Finset R) :
    LocalizedHall N ↔ ∃ f : C ↪ R, ∀ c, f c ∈ N c := by
  rw [LocalizedHall,
    Finset.all_card_le_biUnion_card_iff_existsInjective' N]
  constructor
  · rintro ⟨f, hf, hN⟩
    exact ⟨⟨f, hf⟩, hN⟩
  · rintro ⟨f, hN⟩
    exact ⟨f, f.injective, hN⟩

/-- The structure-valued form of finite Hall's theorem. -/
theorem localizedHall_iff_nonempty_routing {C R : Type*} [Finite C]
    [DecidableEq R] (N : C → Finset R) :
    LocalizedHall N ↔ Nonempty (LocalizedRouting N) := by
  rw [localizedHall_iff_exists_embedding]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨⟨f, hf⟩⟩
  · rintro ⟨⟨f, hf⟩⟩
    exact ⟨f, hf⟩

/-- The resources available to a demand are exactly those with the same
owner. -/
def ownedNeighborhood {C R O : Type*} [Fintype R] [DecidableEq O]
    (ownerC : C → O) (ownerR : R → O) (c : C) : Finset R :=
  Finset.univ.filter fun r => ownerR r = ownerC c

/-- Fiberwise capacity inequalities imply Hall's condition for the
same-owner neighborhood. -/
theorem localizedHall_ownedNeighborhood {C R O : Type*}
    [Fintype C] [Fintype R] [Fintype O]
    [DecidableEq C] [DecidableEq R] [DecidableEq O]
    (ownerC : C → O) (ownerR : R → O)
    (hcard : ∀ o,
      ((Finset.univ : Finset C).filter fun c => ownerC c = o).card ≤
        ((Finset.univ : Finset R).filter fun r => ownerR r = o).card) :
    LocalizedHall (ownedNeighborhood ownerC ownerR) := by
  intro S
  let owners := S.image ownerC
  have hresources :
      (S.biUnion (ownedNeighborhood ownerC ownerR)).card =
        ∑ o ∈ owners,
          ((Finset.univ : Finset R).filter fun r => ownerR r = o).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := ownerR)
      (s := S.biUnion (ownedNeighborhood ownerC ownerR)) (t := owners)]
    · apply Finset.sum_congr rfl
      intro o ho
      congr 1
      ext r
      simp only [mem_filter, mem_biUnion, mem_univ, true_and,
        ownedNeighborhood]
      constructor
      · rintro ⟨⟨c, hc, howner⟩, hro⟩
        exact hro
      · intro hro
        obtain ⟨c, hc, hco⟩ := mem_image.mp ho
        exact ⟨⟨c, hc, hro.trans hco.symm⟩, hro⟩
    · intro r hr
      obtain ⟨c, hc, howner⟩ := mem_biUnion.mp hr
      have howner' : ownerR r = ownerC c := by
        simpa [ownedNeighborhood] using howner
      exact mem_image.mpr ⟨c, hc, howner'.symm⟩
  calc
    S.card = ∑ o ∈ owners, (S.filter fun c => ownerC c = o).card :=
      Finset.card_eq_sum_card_image ownerC S
    _ ≤ ∑ o ∈ owners,
        ((Finset.univ : Finset C).filter fun c => ownerC c = o).card := by
      apply Finset.sum_le_sum
      intro o ho
      apply Finset.card_le_card
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact hc.2
    _ ≤ ∑ o ∈ owners,
        ((Finset.univ : Finset R).filter fun r => ownerR r = o).card := by
      apply Finset.sum_le_sum
      intro o ho
      exact hcard o
    _ = (S.biUnion (ownedNeighborhood ownerC ownerR)).card := hresources.symm

/-- Fiberwise capacity inequalities give an injective same-owner routing. -/
theorem exists_owned_embedding {C R O : Type*}
    [Fintype C] [Fintype R] [Fintype O]
    [DecidableEq C] [DecidableEq R] [DecidableEq O]
    (ownerC : C → O) (ownerR : R → O)
    (hcard : ∀ o,
      ((Finset.univ : Finset C).filter fun c => ownerC c = o).card ≤
        ((Finset.univ : Finset R).filter fun r => ownerR r = o).card) :
    ∃ f : C ↪ R, ∀ c, ownerR (f c) = ownerC c := by
  obtain ⟨f, hf⟩ := (localizedHall_iff_exists_embedding
    (ownedNeighborhood ownerC ownerR)).mp
      (localizedHall_ownedNeighborhood ownerC ownerR hcard)
  exact ⟨f, fun c => by simpa [ownedNeighborhood] using hf c⟩

section Regression

/-- Two nonempty owner fibers, with one spare resource. -/
example : LocalizedHall (ownedNeighborhood
    (fun c : Fin 3 => (⟨c.1 % 2, by omega⟩ : Fin 2))
    (fun r : Fin 4 => (⟨r.1 % 2, by omega⟩ : Fin 2))) := by
  apply localizedHall_ownedNeighborhood
  decide

/-- Owner `2` has empty demand and resource fibers. -/
example : ∃ f : Fin 2 ↪ Fin 2, ∀ c,
    (fun r : Fin 2 => Fin.castLE (show 2 ≤ 3 by omega) r) (f c) =
      (fun d : Fin 2 => Fin.castLE (show 2 ≤ 3 by omega) d) c := by
  apply exists_owned_embedding
  decide

end Regression

end GridGraphs
