import GridGraphs.ResidueTwoUpper.OneGap.RootedEastContact

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.Mixed
open ResidueZero L7 FanSlab BoundarySix.Connected

private def lines := (include_str "MixedRimWave.txt").splitOn "\n"
private def nums (s : String) := ((s.splitOn " ").filterMap String.toNat?).toArray
private def ids := nums (lines.headD "")
private def pool := (lines.drop 1).toArray.map (Std.HashSet.ofArray ∘ nums)
private def marks (s e t d : Nat) :=
  pool[ids[2*(8*(7*s+e)+t)+d]?.getD 0]?.getD ∅
private def code (a b : Nat) := 1024*a+b
private def north (v : Word) := code v.1 v.2.1
private def west (v : Word) := code v.1 v.2.2.1
private def south (v : Word) := code v.2.2.1 v.2.2.2
private def east (v : Word) := code v.2.1 v.2.2.2
private def ns (t : Nat) := if t=0 then [0,1,2,3] else [min 7 (t+3)]
private def ws (t : Nat) := if t=7 then [3,4,5,6,7] else [t-4]
private def init (v : Word) := (v.1==19 || v.1==147) && v.2.1==147
private def possible (s e t : Nat) (v : Word) :=
  ((s==6 && decide (4≤t) && init v) ||
    (ns t).any fun n => (marks (min 6 (s+1)) e n 0).contains (north v)) &&
  ((e==6 && decide (t≤4)) ||
    (ws t).any fun n => (marks s (min 6 (e+1)) n 1).contains (west v))
private def test (s e t : Nat) :=
  (rimBank (12-s) (12-e) false (s==0)).all fun v => !possible s e t v ||
    ((marks s e t 0).contains (south v) && (marks s e t 1).contains (east v))
private theorem checked : ∀ s e : Fin 7, ∀ t : Fin 8, test s e t=true := by native_decide
private theorem terminal : ∀ t : Fin 8, 2≤t.val → (marks 0 0 t 0).isEmpty=true := by native_decide

private def phase (r c : Nat) := min 7 (4*c+4-3*r)
private def dist (h r : Nat) := min 6 (h-2-r)
private theorem fromN (r c : Nat) : phase r c ∈ ns (phase (r+1) c) := by
  unfold ns phase; split <;> simp only [List.mem_cons,List.not_mem_nil,or_false] <;> omega
private theorem fromW (r c : Nat) : phase r c ∈ ws (phase r (c+1)) := by
  unfold ws phase; split <;> simp only [List.mem_cons,List.not_mem_nil,or_false] <;> omega

theorem no_field (h w : Nat) (ht : 8≤h) (wt : 8≤w) (slope : 3*h≤4*w)
    (T : Tiles) (top : ∀ c, c+2≤w → init (word T 0 c)=true)
    (mem : ∀ r c : Nat, r+2≤h → c+2≤w →
      word T r c∈rimBank (endTag h r) (endTag w c) false (r+2==h)) : False := by
  let state (r c : Nat) := south (word T r c)∈marks (dist h r) (dist w c) (phase r c) 0 ∧
    east (word T r c)∈marks (dist h r) (dist w c) (phase r c) 1
  have advance (r c : Nat) (hr : r+2≤h) (hc : c+2≤w)
      (prev : ∀ a b, a+b<r+c → a+2≤h → b+2≤w → state a b) : state r c := by
    have tag (n i : Nat) (fit : i+2≤n) : endTag n i=12-dist n i := by unfold endTag dist; split <;> omega
    have se : (r+2==h)=(dist h r==0) := by apply Bool.eq_iff_iff.mpr; simp [dist]; omega
    have m := mem r c hr hc
    rw [tag h r hr,tag w c hc,se] at m
    have S := checked ⟨dist h r,by unfold dist; omega⟩ ⟨dist w c,by unfold dist; omega⟩
      ⟨phase r c,by unfold phase; omega⟩
    have ck := List.all_eq_true.mp S _ m
    have ok : possible (dist h r) (dist w c) (phase r c) (word T r c)=true := by
      apply Bool.and_eq_true_iff.mpr
      constructor <;> apply Bool.or_eq_true_iff.mpr
      · cases r with
        | zero =>
          left; simp only [top c hc,Bool.and_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
          unfold dist phase; omega
        | succ a =>
          right; apply List.any_eq_true.mpr
          refine ⟨_,fromN a c,?_⟩
          rw [show min 6 (dist h (a+1)+1)=dist h a by unfold dist; omega]
          exact Std.HashSet.contains_iff_mem.mpr (prev a c (by omega) (by omega) hc).1
      · cases c with
        | zero =>
          left; simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]; unfold dist phase; omega
        | succ b =>
          right; apply List.any_eq_true.mpr
          refine ⟨_,fromW r b,?_⟩
          rw [show min 6 (dist w (b+1)+1)=dist w b by unfold dist; omega]
          exact Std.HashSet.contains_iff_mem.mpr (prev r b (by omega) hr (by omega)).2
    simpa only [state,ok,Bool.not_true,Bool.false_or,Bool.and_eq_true,Std.HashSet.contains_iff_mem] using ck
  have cells (r c : Nat) (hr : r+2≤h) (hc : c+2≤w) : state r c := by
    induction n : r+c using Nat.strong_induction_on generalizing r c with
    | h n ih =>
      exact advance r c hr hc (fun a b lt ha hb => ih (a+b) (by omega) a b ha hb rfl)
  have endM := (cells (h-2) (w-2) (by omega) (by omega)).1
  rw [show dist h (h-2)=0 by unfold dist; omega,show dist w (w-2)=0 by unfold dist; omega] at endM
  have empty := terminal ⟨phase (h-2) (w-2),by unfold phase; omega⟩ (by dsimp [phase]; omega)
  exact (Std.HashSet.isEmpty_iff_forall_not_mem.mp empty) _ endM

theorem exclude_suffix {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    (y f : Nat) (yl : 4≤y) (fl : 4≤f) (ht : y+8≤11+14*u) (wt : f+8≤11+14*u)
    (slope : 3*(11+14*u-y)≤4*(11+14*u-f))
    (seed : ∀ i, f ≤ i → i < 11+14*u →
      (tile F v y i=73 ∨ i=f ∧ tile F v y i=9) ∧ RootLine F v i y) : False := by
  let k := 11+14*u
  let t := fun r c => tile F v (y+r) (f+c)
  apply no_field (k-y) (k-f) (by dsimp [k]; omega) (by dsimp [k]; omega) slope (field t)
  · intro c hc
    have a := (seed (f+c) (by omega) (by dsimp [k] at hc; omega)).1
    have b := (seed (f+(c+1)) (by omega) (by dsimp [k] at hc; omega)).1
    have b' : tile F v y (f+(c+1))=73 := by rcases b with h|⟨h,_⟩ <;> omega
    rcases a with h|⟨_,h⟩ <;> simp [init,word,field,flags,t,labelled,b',h]
  · intro r c hr hc
    have m := physical_label_bank_from_second false H acy one score hk y f yl fl (by omega)
      (fun i l h => ⟨by intro lt; rcases (seed i l h).1 with z|⟨z,_⟩ <;> omega,(seed i l h).2⟩) r c hr hc
    exact List.mem_filter.mpr ⟨by simpa only [Bool.and_false] using m,
      physical_east_filter H acy one y f yl fl (by omega) (fun i l h => (seed i l h).2) r c hr hc⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.Mixed
