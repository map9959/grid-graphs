import GridGraphs.ResidueTwoUpper.OneGap.RootedRailStep

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
open ResidueZero L7 FanSlab BoundarySix.Connected

private def pairs : List (Nat × Nat) :=
  [(9,9),(9,73),(16,73),(73,73),(129,9),(129,73),(144,129)]

private def level (m b : Nat) : Nat :=
  if m=73 then 3 else if m=9 ∧ (b=18 ∨ b=146) then 2
  else if (m,b)∈[(9,3),(9,7),(129,18),(129,146)] then 1 else 0

private def join (m b : Nat) : Prop := bit m 3=1 ∧ (bit m 6=1 ∨ bit b 0=1)
private instance (m b : Nat) : Decidable (join m b) := by unfold join; infer_instance

private def bridge (w : Word) : Prop :=
  join w.1 w.2.2.1 ∧ join w.2.1 w.2.2.2 ∧ bit w.2.2.1 1=1 ∧ bit w.2.2.2 0=1
private instance (w : Word) : Decidable (bridge w) := by unfold bridge; infer_instance

private def rule (w : Word) : Prop :=
  (w.1=73 → w.2.1=73 → (w.2.2.1,w.2.2.2)∈pairs) ∧
  ((w.1,w.2.1)∈pairs → ¬bridge w →
    min 3 (level w.1 w.2.2.1+1) ≤ level w.2.1 w.2.2.2)
private instance (w : Word) : Decidable (rule w) := by unfold rule; infer_instance

private theorem tagCheck : ∀ a b : Fin 7,
    (bankWords (6+a.val) (6+b.val)).all (fun w => decide (rule w))=true := by native_decide

def AdmittedWord (w : Word) : Prop := ∃ a b : Fin 7, w∈bankWords (6+a.val) (6+b.val)

private theorem rules {w : Word} (h : AdmittedWord w) : rule w := by
  obtain ⟨a,b,m⟩ := h
  exact of_decide_eq_true (List.all_eq_true.mp (tagCheck a b) _ m)

/-- Under four parallel north-rooted 73 tiles, the fourth tile in
the next row is again a north-rooted 73. Only two plaquette rows
are read. No `Straight`, `DeepAfter`, or interior mask alphabet is
assumed. Catalogue admission is needed at the six named plaquettes. -/
theorem advance_four {u y c} {F : Finset (Site u)} {v : View}
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (ry : 1+3*(y+2)+1<35+42*u) (ct : 1+3*(c+3)+1<35+42*u)
    (upper : ∀ i≤3, tile F v y (c+i)=73 ∧ RootLine F v (c+i) y)
    (bank : ∀ j<2, ∀ i<3, AdmittedWord (word (tile F v) (y+j) (c+i))) :
    tile F v (y+1) (c+3)=73 ∧ RootLine F v (c+3) (y+1) := by
  let t := tile F v
  have root (i : Nat) (hi : i≤3) : RootLine F v (c+i) (y+1) := by
    have old := upper i hi
    apply extend_line old.2
    · rw [old.1]; decide
    · left; rw [old.1]; decide
  have step (i : Nat) (hi : i<3) :
      min 3 (level (t (y+1) (c+i)) (t (y+2) (c+i))+1) ≤
        level (t (y+1) (c+(i+1))) (t (y+2) (c+(i+1))) := by
    let w := word t (y+1) (c+i)
    have lower := (rules (bank 1 (by decide) i hi)).2
    have h := (rules (bank 0 (by decide) i hi)).1 (upper i (by omega)).1
      (by simpa only [word,Nat.add_assoc,Nat.add_zero] using (upper (i+1) (by omega)).1)
    have no : ¬bridge w := by
      rintro ⟨⟨mid₁,cap₁⟩,⟨mid₂,cap₂⟩,arm,head⟩
      have l := extend_line (root i (by omega)) mid₁ cap₁
      have r : RootLine F v (c+i+1) (y+1) := by
        simpa only [Nat.add_assoc] using root (i+1) (by omega)
      exact no_crossbar acy one (by omega) (by omega) l (extend_line r mid₂ cap₂) arm head
    exact lower h no
  have s₀ := step 0 (by decide)
  have s₁ := step 1 (by decide)
  have s₂ := step 2 (by decide)
  simp only [Nat.reduceAdd] at s₀ s₁ s₂
  have high : 3≤level (t (y+1) (c+3)) (t (y+2) (c+3)) := by omega
  refine ⟨?_,root 3 le_rfl⟩
  unfold level at high
  split at high <;> rename_i e
  · exact e
  · split at high <;> (try split at high) <;> omega

/-- The actual north attachment, not just a vertical-looking mask,
is part of the induction invariant at every surviving column. -/
theorem advance_suffix {u y c W d} {F : Finset (Site u)} {v : View}
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (ry : 1+3*(y+d+1)+1<35+42*u) (ct : 1+3*(W-1)+1<35+42*u)
    (upper : ∀ i : Nat, c ≤ i → i < W → tile F v y i=73 ∧ RootLine F v i y)
    (bank : ∀ j<d, ∀ e<2, ∀ a : Nat, c+3*j ≤ a → a+1 < W →
      AdmittedWord (word (tile F v) (y+j+e) a)) :
    ∀ j≤d, ∀ i : Nat, c+3*j ≤ i → i < W → tile F v (y+j) i=73 ∧ RootLine F v i (y+j) := by
  intro j
  induction j with
  | zero => simpa using fun (_ : 0≤d) => upper
  | succ j ih =>
    intro bound i il ir
    have next := advance_four (y:=y+j) (c:=i-3) acy one (by omega) (by omega)
      (fun a ha => ih (by omega) _ (by omega) (by omega))
      (fun e he a ha => bank j (by omega) e he _ (by omega) (by omega))
    simpa only [show i-3+3=i by omega,Nat.add_assoc] using next

/-- At the last tile row there is no lower plaquette. Three incoming
73s suffice to force a vertical head and middle site in the last tile. -/
theorem bottom_carry {t : Tiles} (y c : Nat)
    (upper : ∀ i≤2, t y (c+i)=73)
    (bank : ∀ i<2, AdmittedWord (word t y (c+i))) :
    t (y+1) (c+2)=9 ∨ t (y+1) (c+2)=73 := by
  have a := (rules (bank 0 (by decide))).1 (upper 0 (by decide)) (upper 1 (by decide))
  have b := (rules (bank 1 (by decide))).1 (upper 1 (by decide)) (upper 2 (by decide))
  simp only [word,pairs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,
    Nat.add_zero,Nat.add_assoc,Nat.reduceAdd] at a b
  grind (splits := 24)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
