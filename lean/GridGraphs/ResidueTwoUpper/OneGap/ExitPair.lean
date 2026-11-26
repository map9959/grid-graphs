import GridGraphs.ResidueTwoUpper.OneGap.DepartureRim

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Departure
open ResidueZero BoundarySix.Connected SouthCap SouthCap.Strip SouthCap.Strip.GridScan Rooted

private def exitLaw (w : Word) : Prop :=
  let (a,b,_,d) := w
  ((a=2 ∨ a=32 ∨ a=66) → (b=8 → a=2) ∧ (b=72 → d=9 ∨ d=73)) ∧
    (a=66 → b=72 → w.2.2.1=9 ∨ w.2.2.1=73)
private instance (w) : Decidable (exitLaw w) := by unfold exitLaw; infer_instance
private theorem exits_checked : ∀ r c : Fin 7, (bankWords (6+r.val) (6+c.val)).all
    (fun w => decide (exitLaw w))=true := by native_decide

/-- On the wider fan exit, 8 would be a forbidden `2,8` ending.
The surviving 72 feeds a low head one column farther west below. -/
private theorem law_at {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u) {r c}
    (rl : 4≤r) (cl : 4≤c) (rh : r+2≤11+14*u) (ch : c+2≤11+14*u) :
    exitLaw (Strip.word (tile F v) r c) := by
  have R := tag_range (show r+2≤11+14*u by omega)
  have C := tag_range (show c+2≤11+14*u by omega)
  have T := exits_checked ⟨endTag (11+14*u) r-6,by omega⟩ ⟨endTag (11+14*u) c-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag (11+14*u) r-6)=endTag (11+14*u) r by omega,
    show 6+(endTag (11+14*u) c-6)=endTag (11+14*u) c by omega] at T
  exact of_decide_eq_true
    (List.all_eq_true.mp T _ (board_word H acy score hk rl cl (by omega) (by omega)))
theorem pair_below {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u) {r c}
    (rl : 4≤r) (cl : 4≤c) (rh : r+3≤11+14*u) (ch : c+5≤11+14*u)
    (a : tile F v r c=2 ∨ tile F v r c=32 ∨ tile F v r c=66)
    (b : tile F v r (c+1)=8 ∨ tile F v r (c+1)=72)
    (e : tile F v r (c+2)=9 ∨ tile F v r (c+2)=73)
    (root : RootLine F v (11+14*u-1) r) :
    tile F v (r+1) (c+1)=9 ∨ tile F v (r+1) (c+1)=73 := by
  have law := (law_at H acy one score hk rl cl (by omega) (by omega)).1
  rcases b with eight|s
  · exact (no28 H acy one score hk rl cl rh ch (.inl ((law a).1 eight)) eight e root).elim
  · exact (law a).2 s
theorem pair_plain {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u) {r c}
    (rl : 4≤r) (cl : 4≤c) (rh : r+3≤11+14*u) (ch : c+5≤11+14*u)
    (a : tile F v r c=2 ∨ tile F v r c=32 ∨ tile F v r c=66)
    (b : tile F v r (c+1)=8 ∨ tile F v r (c+1)=72)
    (e : tile F v r (c+2)=9 ∨ tile F v r (c+2)=73)
    (root : RootLine F v (11+14*u-1) r) : tile F v r (c+2)=73 := by
  have law := (law_at H acy one score hk rl cl (by omega) (by omega)).1
  rcases b with eight|s
  · exact (no28 H acy one score hk rl cl rh ch (.inl ((law a).1 eight)) eight e root).elim
  · have h := ray H acy score hk rl (by omega : 4≤c+1) (by omega) (.inr rfl) (.inl s)
        (c+2) (by omega) (by omega)
    omega

theorem sixtySix_below {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u) {r c}
    (rl : 4≤r) (cl : 4≤c) (rh : r+2≤11+14*u) (ch : c+2≤11+14*u)
    (a : tile F v r c=66) (b : tile F v r (c+1)=72) :
    tile F v (r+1) c=9 ∨ tile F v (r+1) c=73 :=
  (law_at H acy one score hk rl cl rh ch).2 a b
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Departure
