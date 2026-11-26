import GridGraphs.ResidueTwoUpper.OneGap.FanLong

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSeed BoundarySix.Connected SimpleGraph GridGraphs.ResidueTwoUpper.Exceptional.Frame

/-- Auxiliary arrows on the actual forced edges. Charges in `front_of_score`
continue to use its original witness; these arrows record the unique route
of an active vertex to the real perimeter. -/
structure Flow {n} (F : Finset (GridVertex n n)) where
  parent : GridVertex n n → GridVertex n n
  rank : GridVertex n n → Nat
  step : ∀ v, parent v≠v → (Bonds F).Adj v (parent v)
  down : ∀ v, parent v≠v → rank (parent v)<rank v
  covers : ∀ v w, (Bonds F).Adj v w → (parent v=w ↔ parent w≠v)
  noExit : ∀ v, IsGridBoundary v → IsGridBoundary (parent v)
  active : ∀ v w, (Bonds F).Adj v w → parent v=v → IsGridBoundary v

theorem flow_of_score (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) : Nonempty (Flow F) := by
  classical
  obtain ⟨P,sink,step,arr,only,d,wd,zero⟩ := single_defect u F acy score
  have corners := corners_marked u F acy score
  have good := frame_checked stars_checked patches_checked u F P acy step corners (fun x => by
    by_cases eq : x=d; exact Or.inr (eq ▸ wd); exact Or.inl (zero _ eq))
  have gap := gap_split (by omega) F P ⟨nw u,Or.inl rfl⟩ corners
    (fun _ _ e => (all_active_reachable u F acy score e).1) sink step arr good d zero
  have exits := (gap.resolve_right (fun h => by omega)).2
  let G := Bonds F
  let R (c : G.ConnectedComponent) := if G.connectedComponentMk (nw u)=c then nw u else c.out
  have sec c : G.connectedComponentMk (R c)=c := by dsimp [R]; split <;> first | assumption | exact Quot.out_eq _
  let Q := CapBill.parent R sec; let rank := CapBill.depth R
  have dst (v) (h : G.Reachable (nw u) v) : CapBill.dest R v=nw u := by simp [CapBill.dest,R,ConnectedComponent.sound h]
  have agree (k : Nat) (v) (dh : rank v=k) (reach : G.Reachable (nw u) v) : P v=Q v := by
    induction k using Nat.strong_induction_on generalizing v with
    | h k ih =>
      by_cases fix : Q v=v
      · have eq := (CapBill.parent_fix R sec v).mp fix; rw [dst v reach] at eq; rw [fix,eq]; exact sink
      have ⟨e,low⟩ := CapBill.parent_step R sec (mt (CapBill.parent_fix R sec v).mpr fix)
      have z := ih (rank (Q v)) (by simpa [←dh] using low) (Q v) rfl (reach.trans e.reachable)
      apply (arr _ _ e).mpr; rw [z]; intro rev
      have e2 := (CapBill.parent_step R sec (mt (CapBill.parent_fix R sec (Q v)).mpr (show Q (Q v)≠Q v from fun h => fix ((rev.symm.trans h).symm)))).2
      change rank (Q (Q v))<rank (Q v) at e2 -- keep the step's strict inequality
      rw [rev] at e2; exact (Nat.lt_asymm e2 low)
  refine ⟨⟨P,rank,step,?_,arr,?_,?_⟩⟩
  · intro v ne; have reach := (all_active_reachable u F acy score (step v ne)).1
    have A := agree _ _ rfl reach; rw [A] at ne ⊢
    exact (CapBill.parent_step R sec (mt (CapBill.parent_fix R sec v).mpr ne)).2
  · intro v bd; by_contra h; have mem : (⟨v,bd⟩ : PerimeterVertex _)∈exitSet P := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    simpa [exits] using mem
  · intro v w e fix; have reach := (all_active_reachable u F acy score e).1
    have A := agree _ _ rfl reach; rw [A] at fix
    have eq := (CapBill.parent_fix R sec v).mp fix; rw [dst v reach] at eq; rw [eq]; exact Or.inl rfl

/-- If a component above the cut has no foot and every crossing leaves
from `v`, its parent must cross at `v`. This applies to a window only at
that actual cut, not to arbitrary separately realizable port labels. -/
theorem forced_exit {n} {F : Finset (GridVertex n n)} (Q : Flow F) (S : Set (GridVertex n n)) (v : S)
    (incident : ∃ w,(Bonds F).Adj v.1 w) (closed : ∀ x : S, ((Bonds F).induce S).Reachable v x → ¬IsGridBoundary x.1)
    (only : ∀ x : S, ((Bonds F).induce S).Reachable v x → ∀ w,(Bonds F).Adj x.1 w → w∉S → x=v) : Q.parent v.1∉S := by
  intro stays
  have loop (k : Nat) (x : S) (rank : Q.rank x.1=k) (reach : ((Bonds F).induce S).Reachable v x)
      (bound : k≤Q.rank v.1) (edge : ∃ w,(Bonds F).Adj x.1 w) : False := by
    induction k using Nat.strong_induction_on generalizing x with
    | h k ih =>
      obtain ⟨w,e⟩ := edge
      have nf : Q.parent x.1≠x.1 := fun h => closed _ reach (Q.active _ _ e h)
      have nx := Q.step _ nf; have drop := Q.down _ nf
      by_cases inp : Q.parent x.1∈S
      · let t : S := ⟨Q.parent x.1,inp⟩; have adj : ((Bonds F).induce S).Adj x t := nx
        exact ih (Q.rank (Q.parent x.1)) (by omega) t rfl (reach.trans adj.reachable) (by omega) ⟨_,nx.symm⟩
      · exact inp ((only _ reach _ nx inp) ▸ stays)
  exact loop _ v rfl .rfl le_rfl incident
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
