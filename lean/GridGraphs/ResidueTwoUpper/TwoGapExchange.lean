import GridGraphs.NoPitch.FaceExchange
import GridGraphs.ResidueTwoUpper.TwoGapCornerExit

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Exchange
open SimpleGraph Finset

/-- Reflect an entire local forest through a permutation of its two
interface vertices. Whether they were joined is invariant under the swap;
the exterior need not be invariant, or even connected. -/
theorem flip_two_ports {V : Type*} [Fintype V] [LinearOrder V]
    (A B E : SimpleGraph V) (box : V → Prop) (p q : V) (f : A →g B)
    (inj : Function.Injective f) (fp : f p=q) (fq : f q=p)
    (inside : ∀ x y, A.Adj x y → box x)
    (outside : ∀ x y, E.Adj x y → ¬B.Adj x y ∧ (box x → x=p ∨ x=q))
    (acy : (B⊔E).IsAcyclic) : (A⊔E).IsAcyclic := by
  classical
  let ext := univ.filter fun e : V × V => e.1<e.2 ∧ E.Adj e.1 e.2
  have eq : NoPitch.exterior ext=E := by
    ext x y; rw [NoPitch.exterior_adj]
    simp only [ext,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨_,a⟩|⟨_,a⟩⟩; exact a; exact a.symm
    · intro a; exact ⟨a.ne,(lt_or_gt_of_ne a.ne).imp (fun h => ⟨h,a⟩) (fun h => ⟨h,a.symm⟩)⟩
  rw [←eq]
  apply NoPitch.forest_glue A B {x | box x → x=p ∨ x=q} _ ((acy.anti le_sup_left).comap f inj)
  · intro e h
    obtain ⟨lt,a⟩ := (mem_filter.mp h).2
    exact ⟨fun h' => lt.asymm (mem_filter.mp h').2.1,(outside _ _ a).2,
      (outside _ _ a.symm).2,(outside _ _ a).1⟩
  · rwa [eq]
  · intro x hx y hy path
    by_cases same : x=y
    · subst y; exact .rfl
    obtain ⟨_,ax⟩ := path.nonempty_neighborSet_left same
    obtain ⟨_,ay⟩ := path.symm.nonempty_neighborSet_left (Ne.symm same)
    have h := path.map f
    rcases hx (inside _ _ ax) with rfl|rfl <;> rcases hy (inside _ _ ay) with rfl|rfl <;>
      simp_all only [not_true_eq_false]
    all_goals exact h.symm

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Exchange
