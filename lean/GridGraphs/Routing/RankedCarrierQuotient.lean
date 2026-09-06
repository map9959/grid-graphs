import GridGraphs.Routing.TerminalCarrierQuotientRouting
import Mathlib.Data.Finset.Max

/-!
# Ranked carrier quotient accounting

A finite occurrence type with an injective natural-number rank has a canonical
representative in each carrier class: the occurrence of minimum rank.  This
file records the resulting exact quotient/collision split.  It also provides a
least-forward-exponent rank for a single orbit of a finite permutation.
-/

namespace GridGraphs

open Finset

universe u v

variable {A : Type u} {K : Type v}

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Least forward exponent from a fixed anchor in a finite permutation orbit. -/
def forwardCycleRank {X : Type*} [Fintype X] (f : Equiv.Perm X) (anchor : X)
    (hcycle : ∀ x, f.SameCycle anchor x) (x : X) : Nat :=
  Nat.find ((hcycle x).exists_nat_pow_eq)

@[simp] theorem forwardCycleRank_spec {X : Type*} [Fintype X]
    (f : Equiv.Perm X) (anchor : X) (hcycle : ∀ x, f.SameCycle anchor x)
    (x : X) :
    (f ^ forwardCycleRank f anchor hcycle x) anchor = x :=
  Nat.find_spec ((hcycle x).exists_nat_pow_eq)

/-- Forward ranks from one anchor distinguish every point in its orbit. -/
theorem forwardCycleRank_injective {X : Type*} [Fintype X]
    (f : Equiv.Perm X) (anchor : X) (hcycle : ∀ x, f.SameCycle anchor x) :
    Function.Injective (forwardCycleRank f anchor hcycle) := by
  intro x y hxy
  rw [← forwardCycleRank_spec f anchor hcycle x,
    ← forwardCycleRank_spec f anchor hcycle y, hxy]

private def rankedCarrierClass [Fintype A] (carrier : A -> K)
    (q : CarrierQuotient carrier) : Finset A :=
  Finset.univ.filter fun a => carrierQuotientMk carrier a = q

private theorem rankedCarrierClass_nonempty [Fintype A] (carrier : A -> K)
    (q : CarrierQuotient carrier) :
    (rankedCarrierClass carrier q).Nonempty := by
  refine ⟨carrierRepresentative carrier q, ?_⟩
  simp [rankedCarrierClass]

/-- The minimum-rank occurrence in a carrier class. -/
def rankedCarrierRepresentative [Fintype A] (carrier : A -> K) (rank : A -> Nat)
    (q : CarrierQuotient carrier) : A :=
  Classical.choose (Finset.exists_min_image (rankedCarrierClass carrier q) rank
    (rankedCarrierClass_nonempty carrier q))

/-- The ranked representative belongs to the carrier class it represents. -/
@[simp] theorem carrierQuotientMk_rankedCarrierRepresentative [Fintype A]
    (carrier : A -> K) (rank : A -> Nat) (q : CarrierQuotient carrier) :
    carrierQuotientMk carrier (rankedCarrierRepresentative carrier rank q) = q := by
  exact (Finset.mem_filter.mp (Classical.choose_spec
    (Finset.exists_min_image (rankedCarrierClass carrier q) rank
      (rankedCarrierClass_nonempty carrier q))).1).2

/-- The selected representative has minimum rank in its carrier class. -/
theorem rankedCarrierRepresentative_rank_le [Fintype A]
    (carrier : A -> K) (rank : A -> Nat) (q : CarrierQuotient carrier)
    {a : A} (ha : carrierQuotientMk carrier a = q) :
    rank (rankedCarrierRepresentative carrier rank q) ≤ rank a := by
  exact (Classical.choose_spec
    (Finset.exists_min_image (rankedCarrierClass carrier q) rank
      (rankedCarrierClass_nonempty carrier q))).2 a (by
        simp [rankedCarrierClass, ha])

/-- Injective ranks make the minimum-rank representative unique. -/
theorem eq_rankedCarrierRepresentative_of_minimal [Fintype A]
    (carrier : A -> K) (rank : A -> Nat) (hrank : Function.Injective rank)
    (q : CarrierQuotient carrier) {a : A}
    (ha : carrierQuotientMk carrier a = q)
    (hmin : ∀ b, carrierQuotientMk carrier b = q -> rank a ≤ rank b) :
    a = rankedCarrierRepresentative carrier rank q := by
  apply hrank
  apply Nat.le_antisymm
  · exact hmin _ (carrierQuotientMk_rankedCarrierRepresentative carrier rank q)
  · exact rankedCarrierRepresentative_rank_le carrier rank q ha

/-- Occurrences other than the unique minimum-rank occurrence in their class. -/
def RankedCarrierCollision [Fintype A] (carrier : A -> K) (rank : A -> Nat) :=
  {a : A // a ≠ rankedCarrierRepresentative carrier rank
    (carrierQuotientMk carrier a)}

/-- With an injective rank, the non-representatives are exactly the occurrences
that have a lower-ranked occurrence in the same carrier class. -/
theorem mem_rankedCarrierCollision_iff_exists_lt [Fintype A]
    (carrier : A -> K) (rank : A -> Nat) (hrank : Function.Injective rank)
    (a : A) :
    a ≠ rankedCarrierRepresentative carrier rank (carrierQuotientMk carrier a) ↔
      ∃ b, carrier b = carrier a ∧ rank b < rank a := by
  constructor
  · intro hne
    let q := carrierQuotientMk carrier a
    let representative := rankedCarrierRepresentative carrier rank q
    have hcarrier : carrier representative = carrier a := by
      exact Quotient.exact
        ((carrierQuotientMk_rankedCarrierRepresentative carrier rank q).trans rfl)
    have hle : rank representative ≤ rank a :=
      rankedCarrierRepresentative_rank_le carrier rank q rfl
    have hrankNe : rank representative ≠ rank a := by
      intro h
      exact hne (hrank h).symm
    exact ⟨representative, hcarrier, Nat.lt_of_le_of_ne hle hrankNe⟩
  · rintro ⟨b, hcarrier, hlt⟩ heq
    have hbq : carrierQuotientMk carrier b = carrierQuotientMk carrier a :=
      Quotient.sound hcarrier
    have hle := rankedCarrierRepresentative_rank_le carrier rank
      (carrierQuotientMk carrier a) hbq
    rw [← heq] at hle
    exact (Nat.not_lt_of_ge hle) hlt

/-- Ranked collisions are invariant under an equivalence that preserves both
the carrier and the rank. -/
def rankedCarrierCollisionEquivOfEquiv
    {B : Type*} {L : Type*} [Fintype A] [Fintype B]
    (carrierA : A -> K) (rankA : A -> Nat)
    (carrierB : B -> L) (rankB : B -> Nat)
    (hrankA : Function.Injective rankA) (hrankB : Function.Injective rankB)
    (e : A ≃ B)
    (carrier_iff : ∀ a₁ a₂, carrierB (e a₁) = carrierB (e a₂) ↔
      carrierA a₁ = carrierA a₂)
    (rank_eq : ∀ a, rankB (e a) = rankA a) :
    RankedCarrierCollision carrierA rankA ≃
      RankedCarrierCollision carrierB rankB where
  toFun collision := ⟨e collision.1, by
    rw [mem_rankedCarrierCollision_iff_exists_lt carrierB rankB hrankB]
    have hcollision := collision.property
    rw [mem_rankedCarrierCollision_iff_exists_lt carrierA rankA hrankA]
      at hcollision
    obtain ⟨previous, hcarrier, hrank⟩ := hcollision
    exact ⟨e previous, (carrier_iff previous collision.1).2 hcarrier, by
      simpa [rank_eq] using hrank⟩⟩
  invFun collision := ⟨e.symm collision.1, by
    rw [mem_rankedCarrierCollision_iff_exists_lt carrierA rankA hrankA]
    have hcollision := collision.property
    rw [mem_rankedCarrierCollision_iff_exists_lt carrierB rankB hrankB]
      at hcollision
    obtain ⟨previous, hcarrier, hrank⟩ := hcollision
    refine ⟨e.symm previous, ?_, ?_⟩
    · exact (carrier_iff (e.symm previous) (e.symm collision.1)).1 (by
        simpa using hcarrier)
    · rw [← rank_eq (e.symm previous), ← rank_eq (e.symm collision.1)]
      simpa using hrank⟩
  left_inv collision := Subtype.ext (e.symm_apply_apply collision.1)
  right_inv collision := Subtype.ext (e.apply_symm_apply collision.1)

instance rankedCarrierCollisionFintype [Fintype A] (carrier : A -> K)
    (rank : A -> Nat) : Fintype (RankedCarrierCollision carrier rank) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Every occurrence is either its class's ranked representative or a ranked
collision retaining the original occurrence label. -/
def rankedCarrierQuotientCollisionEquiv [Fintype A] (carrier : A -> K)
    (rank : A -> Nat) :
    A ≃ CarrierQuotient carrier ⊕ RankedCarrierCollision carrier rank := by
  refine
    { toFun := fun a =>
        if h : a = rankedCarrierRepresentative carrier rank
            (carrierQuotientMk carrier a) then
          Sum.inl (carrierQuotientMk carrier a)
        else
          Sum.inr ⟨a, h⟩
      invFun := fun x => match x with
        | Sum.inl q => rankedCarrierRepresentative carrier rank q
        | Sum.inr a => a.1
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    by_cases h : a = rankedCarrierRepresentative carrier rank
        (carrierQuotientMk carrier a)
    · dsimp
      rw [dif_pos h]
      exact h.symm
    · dsimp
      rw [dif_neg h]
  · intro x
    rcases x with q | a
    · dsimp
      have hmk := carrierQuotientMk_rankedCarrierRepresentative carrier rank q
      have hrep : rankedCarrierRepresentative carrier rank q =
          rankedCarrierRepresentative carrier rank
            (carrierQuotientMk carrier
              (rankedCarrierRepresentative carrier rank q)) :=
        congrArg (rankedCarrierRepresentative carrier rank) hmk.symm
      rw [dif_pos hrep]
      exact congrArg Sum.inl hmk
    · dsimp
      rw [dif_neg a.property]
      exact congrArg Sum.inr (Subtype.ext rfl)

/-- Exact accounting by carrier classes and minimum-rank collisions. -/
theorem card_carrierQuotient_add_card_rankedCollision [Fintype A]
    (carrier : A -> K) (rank : A -> Nat) :
    Fintype.card A = Fintype.card (CarrierQuotient carrier) +
      Fintype.card (RankedCarrierCollision carrier rank) := by
  rw [Fintype.card_congr (rankedCarrierQuotientCollisionEquiv carrier rank),
    Fintype.card_sum]

/-- Ranked and existing arbitrary-representative collisions have equal size. -/
theorem card_rankedCarrierCollision_eq_card_carrierCollision [Fintype A]
    (carrier : A -> K) (rank : A -> Nat) :
    Fintype.card (RankedCarrierCollision carrier rank) =
      Fintype.card (CarrierCollision carrier) := by
  have hr := card_carrierQuotient_add_card_rankedCollision carrier rank
  have hc := card_carrierQuotient_add_card_collision carrier
  omega

/-- Ranked collisions differ from arbitrary-representative collisions only by
the choice of one occurrence in each class. -/
def rankedCarrierCollisionEquivCarrierCollision [Fintype A]
    (carrier : A -> K) (rank : A -> Nat) :
    RankedCarrierCollision carrier rank ≃ CarrierCollision carrier :=
  Fintype.equivOfCardEq
    (card_rankedCarrierCollision_eq_card_carrierCollision carrier rank)

end

end GridGraphs
