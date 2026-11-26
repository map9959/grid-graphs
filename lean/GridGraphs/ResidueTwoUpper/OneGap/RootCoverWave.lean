import GridGraphs.ResidueTwoUpper.OneGap.RootCoverField

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.Wave

private def data := include_str "RootCoverWave.txt"
private def numbers (s : String) : Array Nat :=
  ((s.splitOn " ").filterMap String.toNat?).toArray
private def lines := data.splitOn "\n"
private def ids := numbers (lines.headD "")
private def pool := (lines.drop 1).toArray.map (fun l => Std.HashSet.ofArray (numbers l))

private def marks (s e t : Nat) (right : Bool) : Std.HashSet Nat :=
  let ix := ids[2*(8*(7*s+e)+t)+right.toNat]?.getD 0
  pool[ix]?.getD ∅

private def code (a b : Nat) := 1024*a+b
private def below (v : Word) := code v.2.2.1 v.2.2.2
private def right (v : Word) := code v.2.1 v.2.2.2
private def above (v : Word) := code v.1 v.2.1
private def left (v : Word) := code v.1 v.2.2.1

private def ns (t : Nat) := if t=0 then [0,1,2,3] else [min 7 (t+3)]
private def ws (t : Nat) := if t=7 then [3,4,5,6,7] else [t-4]

private def permitted (s e t : Nat) (top : Bool) (v : Word) :=
  (if top then s==6 && decide (1≤t) else
    (ns t).any fun n => (marks (min 6 (s+1)) e n false).contains (above v)) &&
  ((e==6 && decide (t≤1)) ||
    (ws t).any fun n => (marks s (min 6 (e+1)) n true).contains (left v))

private def verifies (s e t : Nat) (top : Bool) :=
  (labelBank (12-s) (12-e) top (s==0)).all fun v =>
    !permitted s e t top v ||
    ((marks s e t false).contains (below v) && (marks s e t true).contains (right v))

private theorem checked : ∀ s e : Fin 7, ∀ t : Fin 8, ∀ top : Bool, verifies s e t top=true := by
  native_decide

private theorem terminal : (marks 0 0 7 false).isEmpty=true := by native_decide

/-- Clip the signed quantity `4*c-3*r` to `[-1,6]`, biased by one
so the array index is nonnegative. No bound on the board side. -/
private def phase (r c : Nat) := min 7 (4*c+1-3*r)
private def dist (h r : Nat) := min 6 (h-2-r)

private theorem north_phase (r c : Nat) : phase r c ∈ ns (phase (r+1) c) := by
  unfold ns phase
  split <;> simp only [List.mem_cons,List.not_mem_nil,or_false] <;> omega

private theorem west_phase (r c : Nat) : phase r c ∈ ws (phase r (c+1)) := by
  unfold ws phase
  split <;> simp only [List.mem_cons,List.not_mem_nil,or_false] <;> omega

private theorem tag_eq (h r : Nat) (fit : r+2≤h) : endTag h r=12-dist h r := by
  unfold endTag dist; split <;> omega

/-- A full top row attached to distinct north feet cannot extend to
the south boundary in any rectangle of this aspect ratio. Induction
is over physical coordinates, not over the finite table of types. -/
theorem no_field (h w : Nat) (ht : 8≤h) (wt : 8≤w) (slope : 3*h+8≤4*w)
    (T : Tiles) (mem : ∀ r c : Nat, r+2≤h → c+2≤w →
      word T r c∈labelBank (endTag h r) (endTag w c) (r==0) (r+2==h)) : False := by
  let State (r c : Nat) := below (word T r c)∈marks (dist h r) (dist w c) (phase r c) false ∧
    right (word T r c)∈marks (dist h r) (dist w c) (phase r c) true
  have atCell (r c : Nat) (hr : r+2≤h) (hc : c+2≤w)
      (north : ∀ a, r=a+1 → State a c) (west : ∀ b, c=b+1 → State r b) : State r c := by
    let S := dist h r
    let E := dist w c
    let I := phase r c
    have inBank := mem r c hr hc
    have se : (r+2==h)=(S==0) := by
      apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq,S,dist]; omega
    rw [tag_eq h r hr,tag_eq w c hc,se] at inBank
    have chk := checked ⟨S,by dsimp [S,dist]; omega⟩ ⟨E,by dsimp [E,dist]; omega⟩
      ⟨I,by dsimp [I,phase]; omega⟩ (r==0)
    have tested := List.all_eq_true.mp chk _ inBank
    have yes : permitted S E I (r==0) (word T r c)=true := by
      apply Bool.and_eq_true_iff.mpr
      constructor
      · cases r with
        | zero =>
          simp only [beq_self_eq_true,if_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
          dsimp [S,dist,I,phase]; omega
        | succ a =>
          simp only [show (a+1==0)=false by simp, Bool.false_eq_true,if_false]
          apply List.any_eq_true.mpr
          refine ⟨phase a c,north_phase a c,?_⟩
          have edge := (north a rfl).1
          have eq : min 6 (S+1)=dist h a := by dsimp [S,dist]; omega
          rw [eq]
          exact Std.HashSet.contains_iff_mem.mpr edge
      · apply Bool.or_eq_true_iff.mpr
        cases c with
        | zero =>
          left
          simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
          dsimp [E,dist,I,phase]; omega
        | succ b =>
          right
          apply List.any_eq_true.mpr
          refine ⟨phase r b,west_phase r b,?_⟩
          have edge := (west b rfl).2
          have eq : min 6 (E+1)=dist w b := by dsimp [E,dist]; omega
          rw [eq]
          exact Std.HashSet.contains_iff_mem.mpr edge
    simp only [yes,Bool.not_true,Bool.false_or,Bool.and_eq_true,
      Std.HashSet.contains_iff_mem] at tested
    exact tested
  have allRows (r c : Nat) (hr : r+2≤h) (hc : c+2≤w) : State r c := by
    induction r generalizing c with
    | zero =>
      induction c with
      | zero => exact atCell _ _ hr hc (by omega) (by omega)
      | succ c ih => exact atCell _ _ hr hc (by omega) (by rintro b e; cases e; exact ih (by omega))
    | succ r nr =>
      induction c with
      | zero => exact atCell _ _ hr hc (by rintro a e; cases e; exact nr _ (by omega) hc) (by omega)
      | succ c ih =>
        apply atCell _ _ hr hc
        · rintro a e; cases e; exact nr _ (by omega) hc
        · rintro b e; cases e; exact ih (by omega)
  have edge := (allRows (h-2) (w-2) (by omega) (by omega)).1
  have s : dist h (h-2)=0 := by unfold dist; omega
  have e : dist w (w-2)=0 := by unfold dist; omega
  have t : phase (h-2) (w-2)=7 := by unfold phase; omega
  rw [s,e,t] at edge
  exact (Std.HashSet.isEmpty_iff_forall_not_mem.mp terminal) _ edge

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.Wave
