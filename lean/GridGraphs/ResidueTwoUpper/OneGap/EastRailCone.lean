import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayBank

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan

/-- Either orientation of the short or long line through the
northwest corner of a tile. All four satisfy the rail bit condition. -/
def LineTile (m : Nat) : Prop := m=3 ∨ m=7 ∨ m=9 ∨ m=73
instance (m : Nat) : Decidable (LineTile m) := by unfold LineTile; infer_instance

def LocalRule (w : Word) : Prop :=
  LineTile w.1 → LineTile w.2.1 →
    LineTile w.2.2.2 ∨ (w.2.2.1=146 ∧ w.2.2.2=144) ∨ (w.2.2.1=144 ∧ w.2.2.2=129)
instance (w : Word) : Decidable (LocalRule w) := by unfold LocalRule; infer_instance

-- Inspect each of the 49 catalogue tags once, independently of the
-- height, width and number of times the local rule will be applied.
private theorem local_check : ∀ r c : Fin 7,
    (bankWords (6+r.val) (6+c.val)).all (fun w => decide (LocalRule w))=true := by
  native_decide

theorem bank_local_rule {r c : Nat} {w : Word} (hr : 6≤r ∧ r≤12)
    (hc : 6≤c ∧ c≤12) (hw : w∈bankWords r c) : LocalRule w := by
  let a : Fin 7 := ⟨r-6,by omega⟩
  let b : Fin 7 := ⟨c-6,by omega⟩
  have check := local_check a b
  rw [show 6+a.val=r by dsimp [a]; omega,show 6+b.val=c by dsimp [b]; omega] at check
  exact of_decide_eq_true (List.all_eq_true.mp check w hw)

/-- Three matching plaquettes cannot have a bad southeast output
under four line tiles. A 129 would need a 144 immediately west;
the 144 would need a 146 even farther west, which no rule outputs. -/
theorem line_three {t : Tiles} (r c : Nat)
    (rules : ∀ j, c≤j → j<c+3 → LocalRule (word t r j))
    (top : ∀ j, c≤j → j≤c+3 → LineTile (t r j)) :
    LineTile (t (r+1) (c+3)) := by
  have atCol (j : Nat) (lo : c≤j) (hi : j<c+3) :
      LineTile (t (r+1) (j+1)) ∨
      (t (r+1) j=146 ∧ t (r+1) (j+1)=144) ∨
      (t (r+1) j=144 ∧ t (r+1) (j+1)=129) :=
    rules j lo hi (top j lo (by omega)) (top (j+1) (by omega) (by omega))
  have a := atCol c (by omega) (by omega)
  have b := atCol (c+1) (by omega) (by omega)
  have d := atCol (c+2) (by omega) (by omega)
  simp only [Nat.add_assoc,Nat.reduceAdd,LineTile] at a b d ⊢
  clear atCol rules top
  grind (splits := 24)

/-- A suffix loses at most three columns per row. This is an
induction over arbitrary dimensions, not a sweep at fixed heights. -/
theorem line_cone (t : Tiles) (r c W rows : Nat)
    (top : ∀ j, c≤j → j<W → LineTile (t r j))
    (rules : ∀ k<rows, ∀ j, c+3*k≤j → j+1<W → LocalRule (word t (r+k) j)) :
    ∀ k≤rows, ∀ j, c+3*k≤j → j<W → LineTile (t (r+k) j) := by
  intro k
  induction k with
  | zero => intro _; simpa using top
  | succ k ih =>
    intro fit j lo hi
    have step := line_three (r+k) (j-3)
      (fun a al ah => rules k (by omega) a (by omega) (by omega))
      (fun a al ah => ih (by omega) a (by omega) (by omega))
    simpa only [show j-3+3=j by omega,Nat.add_assoc] using step

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
