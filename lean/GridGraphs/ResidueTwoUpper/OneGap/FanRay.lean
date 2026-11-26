import GridGraphs.ResidueTwoUpper.OneGap.FanStripe

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero Stencil

/-- The complete interval downstream of a mask-7 seed in the physical
bulk. In the star case every patch is clean; in the patch case the ray is
still valid whenever the one charged origin is off its tube. -/
theorem stripe_ray (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (r c length : Nat)
    (hr : 6≤r ∧ r+3*length+8≤33+42*u) (hc : 6≤c ∧ c+9≤33+42*u)
    (phase : r%3=1 ∧ c%3=0)
    (clean : ∀ (s : Nat) (_hs : s<length), ∀ i : Fin 5, ∀ j : Fin 3,
      patchSlack F (⟨r+3*s+i,by have := i.isLt; omega⟩,⟨c+j,by have := j.isLt; omega⟩)=0)
    (seed : physicalMask F r (c+1) (by omega) (by omega)=7) :
    physicalMask F (r+3*length) (c+1) (by omega) (by omega)=7 := by
  have go (s : Nat) (le : s≤length) :
      physicalMask F (r+3*s) (c+1) (by omega) (by omega)=7 := by
    induction s with
    | zero => exact seed
    | succ s ih =>
      exact forward_stripe u F acy (r+3*s) c ⟨by omega,by omega⟩ hc
        ⟨by omega,phase.2⟩ (clean s (by omega)) (ih (by omega))
  exact go length le_rfl

/-- Across the exceptional square all clean rays propagate simultaneously.
There is at most one exceptional patch origin for the entire forest, not
one exception per ray. -/
theorem rays_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (BoundarySix.Connected.perimeterHoles F).card=1) :
    let n := 35+42*u
    ∃ (P : GridVertex n n → GridVertex n n) (d : occurrence n),
      GridGraphs.ResidueTwoUpper.Exceptional.Frame.exitSet P=∅ ∧ weightAt F P d=full ∧
      (∀ x, x≠d → weightAt F P x=0) ∧
      ∀ (r c l : Nat) (hr : 6≤r ∧ r+3*l+8≤33+42*u) (hc : 6≤c ∧ c+9≤33+42*u),
        r%3=1 ∧ c%3=0 →
        (∀ (s : Nat) (_ : s<l) (i : Fin 5) (j : Fin 3),
          Sum.inr (⟨r+3*s+i,by have := i.isLt; dsimp [n]; omega⟩,
            ⟨c+j,by have := j.isLt; dsimp [n]; omega⟩)≠d) →
        physicalMask F r (c+1) (by omega) (by omega)=7 →
        physicalMask F (r+3*l) (c+1) (by omega) (by omega)=7 := by
  obtain ⟨P,d,_,_,full',zero,_,cases⟩ :=
    GridGraphs.ResidueTwoUpper.Exceptional.Frame.frame_of_score u F acy score
  refine ⟨P,d,(cases.resolve_right (by rintro ⟨h,_⟩; omega)).2,full',zero,?_⟩
  intro r c l hr hc phase clear' seed
  exact stripe_ray u F acy r c l hr hc phase
    (fun s h i j => zero _ (clear' s h i j)) seed

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
