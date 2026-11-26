import GridGraphs.ResidueTwoUpper.OneGap.EastBoundaryRows
import GridGraphs.ResidueTwoUpper.OneGap.ExitPair

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
open ResidueZero L7 FanSlab FanSweep Short BoundarySix.Connected SouthCap
open SouthCap.Strip.GridScan

/-- First row beyond the open fan. Only the known portions of the
two preceding words are planted; the western side stays open. -/
private def pin (p r c m : Nat) :=
  r%3 != 0 || r>3 || c%3 != 0 || c/3+p+3-r<8 || m==edge (11-r) (c/3)
private def exitGrid (p : Nat) := FanSweep.build (box 8 6) fun r c =>
  ((priceTable[5+(r+1)%3]!)[(c+1)%3]!).filter (pin p r c)
private def col (p : Nat) := if p=1 then 8 else if p=3 then 6 else 5
private def checkExit (p : Nat) :=
  (cell (Kernel.prune 16 43 60 (exitGrid p)) 6 (3*col p)).all fun m => m==9 || m==73
private theorem exit_checked : [1,3,4,5,7].all checkExit := by native_decide
private theorem west_checked :
    let f := Kernel.prune 16 43 60 (exitGrid 5)
    (cell f 6 9).all (fun m => m==2 || m==32 || m==66) &&
    (cell f 6 12).all (fun m => m==8 || m==72) := by native_decide
private theorem seven_checked :
    let f := Kernel.prune 16 43 60 (exitGrid 7)
    (cell f 6 9).all (·==66) && (cell f 6 12).all (·==72) := by native_decide

private def pick (q y d : Nat) := if 6*y+d+7≤q+2 then 7 else
  if 6*y+d+5≤q+2 then 5 else if 6*y+d+4≤q+2 then 4 else if 6*y+d+3≤q+2 then 3 else 1

def exitRoom (u q : Nat) : Prop :=
  let k := 11+14*u; let y := (q-3)/6
  let d := if 35≤q then 1 else 4
  let p := pick q y d
  53≤k ∧ 3≤y ∧ 6*y+d+1≤q+2 ∧ q+17≤k ∧
    (q+2-3*y-8+col p+1+topWidth (k-(y+2))≤k ∨
      (p=5 ∨ p=7) ∧ q+2-3*y-8+(if p=7 then 4 else 5)+topWidth (k-(y+3))≤k)
instance (u q) : Decidable (exitRoom u q) := by unfold exitRoom; infer_instance

private theorem edge_shift (x a b : Nat) : edge (x+a) (x+b)=edge a b := by
  unfold edge; split_ifs <;> first | rfl | omega

set_option maxHeartbeats 900000 in
private theorem chart_live {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {y x d p : Nat} (yl : 3≤y) (fan : 6*y+3≤q) (room : q+6≤11+14*u)
    (offset : q+2=x+8+3*y) (dval : d=4 ∨ (d=1 ∧ 35≤q)) (pad : 3*y+d+p≤x+8) :
    ∀ r<16, ∀ c<43, square F w (1+3*(y-1)+r) (1+3*x+c) ∈
      Kernel.get (Kernel.prune 16 43 60 (exitGrid p)) r c := by
  let z := y-1
  let M := fun r c => square F w (1+3*z+r) (1+3*x+c)
  have init (r : Nat) (hr : r<16) (c : Nat) (hc : c<43) : M r c∈Kernel.get (exitGrid p) r c := by
    have reg := accept_bulk u (3*z+r) (3*x+c) (by dsimp [z]; omega) (by omega)
      F acy P S.step w S.clean (by
        intro v loc; apply S.zero; rw [loc]; intro e
        cases w with | mk aa bb sw => cases aa <;> cases bb <;> cases sw <;>
          simp [L7.view,reflect] at e <;> dsimp [z] at * <;> omega)
    rw [show rowTag (3*z+r)=5+(r+1)%3 by unfold rowTag; dsimp [z]; split <;> omega,
      show realTag u (3*x+c)=5+(c+1)%3 by unfold realTag; split_ifs <;> omega] at reg
    have valid : accepts (5+(r+1)%3) (5+(c+1)%3) (M r c) := by simpa only [M,Nat.add_assoc] using reg
    have pinned : pin p r c (M r c) := by
      unfold pin
      simp only [Bool.or_eq_true,bne_iff_ne,decide_eq_true_eq,beq_iff_eq]
      by_contra! neg
      obtain ⟨⟨⟨⟨rp,rl⟩,cp⟩,en⟩,ne⟩ := neg
      have phys := rows_restart S acy dval (start:=2) (.inr (by omega)) (by intro r l h; omega) (z+r/3) (by dsimp [z]; omega)
        (by dsimp [z]; omega) (x+c/3) (by dsimp [z]; omega) (by omega)
      have E : edge (q+2-3*(z+r/3)) (x+c/3)=edge (11-r) (c/3) := by
        rw [show q+2-3*(z+r/3)=x+(11-r) by dsimp [z]; omega,edge_shift]
      apply ne; rw [←E,←phys]; dsimp [M,maskAtTile]; congr 1 <;> omega
    have bd : M r c<512 := (unpack _).1
    simpa [Kernel.get,exitGrid,FanSweep.build,box,priceTable,hr,hc,
      show 5+(r+1)%3<8 by omega,show (c+1)%3<3 by omega,bd,valid,pinned]
  have live := flat_sound M (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+3*z+r) (1+3*x+c) true)
    (fun r c _ _ => by simpa [M,Nat.add_assoc] using square_meet F w (1+3*z+r) (1+3*x+c) false) 60 _ init
  exact live

theorem exit_head {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {y x : Nat} (yl : 3≤y) (big : 35≤q) (fan : 6*y+3≤q) (room : q+6≤11+14*u)
    (offset : q+2=x+8+3*y) :
    maskAtTile F w (y+1) (x+5)=9 ∨ maskAtTile F w (y+1) (x+5)=73 := by
  have hit := chart_live S acy yl fan room offset (.inr ⟨rfl,big⟩) (p:=4) (by omega)
    6 (by decide) 15 (by decide)
  have ck : checkExit 4 := List.all_eq_true.mp exit_checked 4 (by decide)
  have read := List.all_eq_true.mp ck _ hit
  simpa only [Bool.or_eq_true,beq_iff_eq,maskAtTile,
    show 1+3*(y-1)+6=1+3*(y+1) by omega,show 1+3*x+15=1+3*(x+5) by omega] using read

theorem wide_exit_tiles {u q F P w} (S : Seed (u:=u) F P w q) (acy : (Bonds F).IsAcyclic)
    {y x : Nat} (yl : 3≤y) (big : 35≤q) (fan : 6*y+4≤q) (room : q+6≤11+14*u)
    (offset : q+2=x+8+3*y) :
    (maskAtTile F w (y+1) (x+3)=2 ∨ maskAtTile F w (y+1) (x+3)=32 ∨ maskAtTile F w (y+1) (x+3)=66) ∧
    (maskAtTile F w (y+1) (x+4)=8 ∨ maskAtTile F w (y+1) (x+4)=72) ∧
    (maskAtTile F w (y+1) (x+5)=9 ∨ maskAtTile F w (y+1) (x+5)=73) := by
  have hit (c : Nat) (hc : c≤14) : maskAtTile F w (y+1) (x+c)∈
      cell (Kernel.prune 16 43 60 (exitGrid 5)) 6 (3*c) := by
    have h := chart_live S acy yl (by omega) room offset (.inr ⟨rfl,big⟩) (p:=5) (by omega)
      6 (by decide) (3*c) (by omega)
    simpa only [cell,Kernel.get,maskAtTile,show 1+3*(y-1)+6=1+3*(y+1) by omega,
      show 1+3*x+3*c=1+3*(x+c) by omega] using h
  have A := List.all_eq_true.mp (Bool.and_eq_true_iff.mp west_checked).1 _ (hit 3 (by decide))
  have B := List.all_eq_true.mp (Bool.and_eq_true_iff.mp west_checked).2 _ (hit 4 (by decide))
  have C := List.all_eq_true.mp (List.all_eq_true.mp exit_checked 5 (by decide)) _ (hit 5 (by decide))
  simpa only [Bool.or_eq_true,beq_iff_eq,or_assoc] using And.intro A (And.intro B C)

set_option maxHeartbeats 900000 in
theorem exclude_exit {u q F P w} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (ok : exitRoom u q) : False := by
  let k := 11+14*u; let y := (q-3)/6; let x := q+2-3*y-8
  let d := if 35≤q then 1 else 4
  let p := pick q y d
  change 53≤k ∧ 3≤y ∧ 6*y+d+1≤q+2 ∧ q+17≤k ∧ (x+col p+1+topWidth (k-(y+2))≤k ∨
    (p=5 ∨ p=7) ∧ x+(if p=7 then 4 else 5)+topWidth (k-(y+3))≤k) at ok
  obtain ⟨hk,yl,center,room,width⟩ := ok
  have offset : q+2=x+8+3*y := by dsimp [x]; omega
  have dval : d=4 ∨ (d=1 ∧ 35≤q) := by dsimp [d]; split <;> omega
  have fan : 6*y+3≤q := by dsimp [y] at *; omega
  have pad : 3*y+d+p≤x+8 := by dsimp [p,pick]; split_ifs <;> omega
  have kind : p∈[1,3,4,5,7] := by dsimp [p,pick]; split_ifs <;> decide
  have cl : col p≤8 := by dsimp [col]; split_ifs <;> decide
  let z := y-1
  let M := fun r c => square F w (1+3*z+r) (1+3*x+c)
  have live := chart_live S acy yl fan (by dsimp [k] at *; omega) offset dval pad
  change ∀ r<16, ∀ c<43, M r c∈Kernel.get (Kernel.prune 16 43 60 (exitGrid p)) r c at live
  have ck : checkExit p := List.all_eq_true.mp exit_checked _ kind
  have hit := Bool.or_eq_true_iff.mp (List.all_eq_true.mp ck _ (live 6 (by decide) (3*col p) (by omega)))
  change (M 6 (3*col p)==9)=true ∨ (M 6 (3*col p)==73)=true at hit
  simp only [beq_iff_eq,M,show 1+3*z+6=1+3*(y+1) by dsimp [z]; omega,
    show 1+3*x+3*col p=1+3*(x+col p) by omega] at hit
  have line := last_line S acy hk room yl (by omega)
  have tail := Departure.plainBeyond H acy one score (by omega) (r:=y+1) (c:=x+col p)
    (by omega) (by omega) (by dsimp [k] at *; omega) (by dsimp [k] at *; omega) hit line
  have plain := CornerCone.low_head H acy one score (by omega) (r:=y+1) (x:=x+col p)
    (by omega) (by omega) (by dsimp [k] at *; omega) (by dsimp [k] at *; omega) hit
    (fun i lo hi => tail i (by omega) hi) line
  have last := tail (k-1) (by omega) (by omega)
  have next := Rooted.extend_line line (by rw [last]; decide) (.inl (by rw [last]; decide))
  rcases width with width|⟨wide,width⟩
  · exact trimmed_excludes_of_ge53 H acy one score hk (by omega) (by omega) (by dsimp [k] at *; omega)
      width plain next
  · have a := live 6 (by decide) 9 (by decide)
    have b := live 6 (by decide) 12 (by decide)
    let t := if p=7 then 3 else 4
    have tb : t=3 ∨ t=4 := by dsimp [t]; split <;> simp
    have low : Rooted.tile F w (y+2) (x+t)=9 ∨ Rooted.tile F w (y+2) (x+t)=73 := by
      have rr : 1+3*z+6=1+3*(y+1) := by dsimp [z]; omega
      have Aeq : M 6 9=Rooted.tile F w (y+1) (x+3) := by
        exact congrArg₂ (square F w) rr (by omega)
      have Beq : M 6 12=Rooted.tile F w (y+1) (x+3+1) := by
        exact congrArg₂ (square F w) rr (by omega)
      rcases wide with five|seven
      · rw [five] at a b hit; simp only [t,five,ite_false,show ¬(5:Nat)=7 by decide]
        have A := List.all_eq_true.mp (Bool.and_eq_true_iff.mp west_checked).1 _ a
        have B := List.all_eq_true.mp (Bool.and_eq_true_iff.mp west_checked).2 _ b
        simp only [Bool.or_eq_true,beq_iff_eq,Aeq,Beq] at A B
        exact Departure.pair_below H acy one score (by omega) (r:=y+1) (c:=x+3)
          (by omega) (by omega) (by dsimp [k] at *; omega) (by dsimp [k] at *; omega)
          (or_assoc.mp A) B (by simpa [col,Nat.add_assoc] using hit) line
      · rw [seven] at a b; simp only [t,seven,ite_true]
        have A := beq_iff_eq.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp seven_checked).1 _ a)
        have B := beq_iff_eq.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp seven_checked).2 _ b)
        exact Departure.sixtySix_below H acy one score (by omega) (r:=y+1) (c:=x+3)
          (by omega) (by omega) (by dsimp [k] at *; omega) (by dsimp [k] at *; omega)
          (Aeq ▸ A) (Beq ▸ B)
    have ray := Departure.plainBeyond H acy one score (by omega) (r:=y+2) (c:=x+t)
      (by omega) (by omega) (by dsimp [k] at *; omega) (by dsimp [k] at *; omega) low next
    have ray' := CornerCone.low_head H acy one score (by omega) (r:=y+2) (x:=x+t)
      (by omega) (by omega) (by dsimp [k] at *; omega) (by dsimp [k] at *; omega)
      low (fun i lo hi => ray i (by omega) hi) next
    have last' := ray (k-1) (by omega) (by omega)
    exact trimmed_excludes_of_ge53 H acy one score hk (by omega) (by omega) (by dsimp [k] at *; omega)
      (a:=x+t+1) (by dsimp [t]; by_cases e : p=7 <;> simp [e,Nat.add_assoc] at width ⊢ <;> exact width) ray'
      (Rooted.extend_line next (by rw [last']; decide) (.inl (by rw [last']; decide)))
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
