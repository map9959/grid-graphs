import GridGraphs.ResidueTwoUpper.OneGap.DepartureOwners
import GridGraphs.ResidueTwoUpper.OneGap.CornerDrift

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Departure
open ResidueZero FanSlab BoundarySix.Connected SouthCap SouthCap.Strip
open SouthCap.Strip.GridScan SouthCap.Strip.GridScan.Rooted SouthCap.Strip.GridScan.Rooted.Buffered
private def tailLaw (w : Word) : Prop :=
  let (a,b,c,d) := w
  (a=32 → b=2 → d=3 ∨ d=7) ∧ (a=2 → b=73 → c≠7 ∧ (c=3 → d=9 ∨ d=73)) ∧
  (a=292 → b=128 → d=32 ∨ d=128 ∨ d=288) ∧
  (a=128 → b=9 → c≠128 ∧ ((c=32 ∨ c=288) → d=2 ∨ d=6)) ∧
  (a=9 → b=73 → c≠6 ∧ (c=2 → d=9 ∨ d=73)) ∧
  (a=128 → b=73 → (c=8 ∨ c=72 ∨ c=128) ∧ (d=9 ∨ d=73)) ∧
  (a=129 → b=73 → d=9 ∨ d=73)
set_option synthInstance.maxSize 4096 in
private instance (w) : Decidable (tailLaw w) := by unfold tailLaw; infer_instance
private theorem checks : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (tailLaw w))=true := by native_decide
section
variable {u F v q} (H : PhysicalHalo u F v q (fanDirection u v)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
local notation "K" => (11+14*u)
local notation "t" => (tile F v)
include H acy score hk
private theorem localAt {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K) :
    tailLaw (Strip.word t r c) := by
  have R := tag_range rh; have C := tag_range ch
  have T := checks ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at T
  exact of_decide_eq_true (List.all_eq_true.mp T _ (board_word H acy score hk rl cl rh ch))
include one
/-- A first departure of type 32 can have its required east parent
locally, but not this continuation to the actual rooted east rim. -/
theorem no_32_tail {r x : Nat} (rl : 4≤r) (xl : 4≤x) (rh : r+3≤K) (xh : x+4≤K)
    (bad : t r x=32) (two : t r (x+1)=2) (plain : ∀ i, x+2 ≤ i → i<K → t r i=73)
    (root : RootLine F v (K-1) r) : False := by
  have T := (localAt H acy score hk rl xl (by omega) (by omega)).1 bad two
  have B := plain (x+2) le_rfl (by omega)
  have S := (localAt H acy score hk rl (by omega : 4≤x+1) (by omega) (by omega)).2.1 two B
  have three := T.resolve_right S.1
  have edge : edge₃ (t r (x+2)) (t (r+1) (x+2)) := by
    rw [B]; rcases S.2 three with m|m <;> rw [m] <;> decide
  have row : BandRow t r (x+2) K := by
    intro i l h; rw [plain i l (by omega),plain (i+1) (by omega) (by omega)]; decide
  have next := (across H acy score hk rl (by omega) (by omega) row edge).1
  have new : BandRow t (r+1) (x+1) K := by
    intro i l h
    by_cases e : i=x+1
    · subst i; rw [three]; rcases S.2 three with m|m <;> rw [m] <;> decide
    · exact next i (by omega) h
  have last := plain (K-1) (by omega) (by omega)
  exact no_latch H acy one score hk (by omega) (by omega) (by omega) (by omega) new (.inl three)
    (extend_line root (by rw [last]; decide) (.inl (by rw [last]; decide)))

/-- Both ancestry sources yield the same three straight rows after a
129. On the third row, the only apparent nonshape at the read edge
is 32; the rooted perimeter argument rules it out. -/
theorem three_after {r x : Nat} (rl : 4≤r) (xl : 6≤x) (rh : r+7≤K) (xh : x+8≤K)
    (top : ∀ i, x ≤ i → i<K → t r i=73) (root : RootLine F v (K-1) r)
    (hit : t (r+1) x=129) :
    ∀ d, 1≤d → d≤3 → ∀ i, x ≤ i → i<K → t (r+d) i∈Port.shapes := by
  have force := Break129.forced_corner H acy one score hk rl (by omega) (by omega) (by omega) top hit root
  have first := (CornerCone.step_head H acy one score hk rl (by omega) (by omega) (by omega) top root).2
  have extend {y a : Nat} (plain : ∀ i, a ≤ i → i<K → t y i=73) (al : a<K)
      (line : RootLine F v (K-1) y) := by
    have last := plain (K-1) (by omega) (by omega)
    exact extend_line line (by rw [last]; decide) (.inl (by rw [last]; decide))
  have line1 := extend top (by omega) root
  have line2 := extend first (by omega) line1
  have second := (CornerCone.step_head H acy one score hk (by omega) (by omega) (by omega) (by omega) first line1).2
  have line3 := extend second (by omega) line2
  have third := (CornerCone.step_head H acy one score hk (by omega) (by omega) (by omega) (by omega) second line2).2
  have head2 := (localAt H acy score hk (by omega : 4≤r+1) (by omega : 4≤x) (by omega) (by omega)).2.2.2.2.2.2 hit force.1
  have Fst (i) (l : x ≤ i) (h : i<K) : t (r+1) i∈Port.shapes := by
    by_cases e : i=x
    · rw [e,hit]; decide
    · rw [first i (by omega) h]; decide
  have Snd (i) (l : x ≤ i) (h : i<K) : t (r+2) i∈Port.shapes := by
    by_cases e : i=x
    · rw [e,force.2.1]; decide
    by_cases e : i=x+1
    · subst i; rcases head2 with m|m <;> rw [m] <;> decide
    · rw [second i (by omega) h]; decide
  have L := (localAt H acy score hk (by omega : 4≤r+2) (by omega : 4≤x-1) (by omega) (by omega)).2.2.1
  rw [show x-1+1=x by omega] at L
  have tail := L force.2.2.2.2 force.2.1
  have W := localAt H acy score hk (by omega : 4≤r+2) (by omega : 4≤x) (by omega) (by omega)
  have E := localAt H acy score hk (by omega : 4≤r+2) (by omega : 4≤x+1) (by omega) (by omega)
  have marks : (t (r+3) x=128 ∨ t (r+3) x=288) ∧
      (t (r+3) (x+1)=2 ∨ t (r+3) (x+1)=9 ∨ t (r+3) (x+1)=73) ∧
      (t (r+3) (x+2)=9 ∨ t (r+3) (x+2)=73) := by
    rcases head2 with nine|full
    · have A := W.2.2.2.1 force.2.1 nine
      have B := E.2.2.2.2.1 nine (second _ le_rfl (by omega))
      have two := (A.2 (tail.imp_right (fun p => p.resolve_left A.1))).resolve_right B.1
      have plain : ∀ i, x+2 ≤ i → i<K → t (r+3) i=73 := by
        intro i l h
        by_cases e : i=x+2
        · subst i; apply (B.2 two).resolve_left; intro bad
          exact CornerCone.no_end9 H acy one score hk (by omega) (by omega) (by omega) (by omega) (.inl two) bad third line3
        · exact third i (by omega) h
      have no32 := fun bad => no_32_tail H acy one score hk (by omega) (by omega) (by omega) (by omega) bad two plain line3
      exact ⟨tail.resolve_left no32,.inl two,.inr (plain _ le_rfl (by omega))⟩
    · have A := W.2.2.2.2.2.1 force.2.1 full
      have cap := (CornerCone.step_head H acy one score hk (a:=x+1) (r:=r+2)
        (by omega) (by omega) (by omega) (by omega) (fun i l h => by
          by_cases e : i=x+1
          · exact e ▸ full
          · exact second i (by omega) h) line2).2
      change t (r+3) x=32 ∨ t (r+3) x=128 ∨ t (r+3) x=288 at tail
      have types : t (r+3) x=8 ∨ t (r+3) x=72 ∨ t (r+3) x=128 := A.1
      exact ⟨.inl (by omega),.inr A.2,.inr (cap _ le_rfl (by omega))⟩
  intro d dl dh i l h
  rcases (show d=1 ∨ d=2 ∨ d=3 by omega) with rfl|rfl|rfl
  · exact Fst i l h
  · exact Snd i l h
  by_cases e : i=x
  · subst i; rcases marks.1 with m|m <;> rw [m] <;> decide
  by_cases e : i=x+1
  · subst i; rcases marks.2.1 with m|m|m <;> rw [m] <;> decide
  by_cases e : i=x+2
  · subst i; rcases marks.2.2 with m|m <;> rw [m] <;> decide
  · rw [third i (by omega) h]; decide
end
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Departure
