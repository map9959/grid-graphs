import GridGraphs.ResidueTwoUpper.OneGap.Break129

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CornerCone
open ResidueZero BoundarySix.Connected SouthCap SouthCap.Strip SouthCap.Strip.GridScan
open SouthCap.Strip.GridScan.Rooted SouthCap.Strip.GridScan.Rooted.Buffered
private def law (w : Word) : Prop :=
  let (a,b,c,d) := w
  a=73 → b=73 → edge₃ a c=true ∨ (c=16 ∧ d=73) ∨ c=129 ∨ d=129
private instance (w) : Decidable (law w) := by unfold law; infer_instance
private theorem test : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (law w))=true := by native_decide

private def rimTriple (a b c : Nat) : Prop :=
  (a=16 ∧ b=16 ∧ c=292) ∨ ((a=258 ∨ a=288 ∨ a=292) ∧ b=292 ∧ c=292)
private def westLaw (w : Word) : Prop :=
  let (a,b,c,d) := w
  ((b=16 ∨ b=292) → d=292 → a=292 ∧ c=292) ∧
    ((b=16 ∧ d=16 ∨ (b=258 ∨ b=288 ∨ b=292) ∧ d=292) →
      c=292 → a=258 ∨ a=288 ∨ a=292) ∧
    (c=16 → d=73 → (b=73 ∨ b=9) → b=73 ∧ (a=16 ∨ a=73)) ∧
    (b=73 → d=16 → a=2 ∧ c=258)
set_option synthInstance.maxSize 2048 in
private instance (w) : Decidable (westLaw w) := by unfold westLaw; infer_instance
private theorem westCheck : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (westLaw w))=true := by native_decide

section
variable {u F v q} (H : PhysicalHalo u F v q (fanDirection u v)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
local notation "K" => (11+14*u)
local notation "t" => (tile F v)
include H acy one score hk
omit one in
private theorem westWord {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K) :
    westLaw (Strip.word t r c) := by
  have R := tag_range rh; have C := tag_range ch
  have T := westCheck ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at T
  exact of_decide_eq_true (List.all_eq_true.mp T _ (board_word H acy score hk rl cl rh ch))

omit one in
/-- The corner demands an unbroken western 292 stripe on BOTH lower
rows, not just the nearest western tile. Column four is the first
eligible physical catalogue column. -/
theorem west_trace {r b : Nat} (rl : 4≤r) (rh : r+3≤K) (bh : b<K)
    (A : t r b=16) (B : t (r+1) b=16) (C : t (r+2) b=292) :
    ∀ i, 4 ≤ i → i < b → (t r i=258 ∨ t r i=288 ∨ t r i=292) ∧
      t (r+1) i=292 ∧ t (r+2) i=292 := by
  have go (i : Nat) (il : 4 ≤ i) (ih : i≤b) : rimTriple (t r i) (t (r+1) i) (t (r+2) i) := by
    induction dist : b-i using Nat.strong_induction_on generalizing i
    rename_i n ind
    by_cases end' : i=b
    · subst i; exact .inl ⟨A,B,C⟩
    have old := ind (b-(i+1)) (by omega) (i+1) (by omega) (by omega) rfl
    have W := westWord H acy score hk (by omega : 4≤r+1) il rh (by omega)
    have V := westWord H acy score hk rl il (by omega) (by omega)
    rcases old with ⟨a,b,c⟩|⟨a,b,c⟩
    · have both := W.1 (.inl b) c
      exact .inr ⟨V.2.1 (.inl ⟨a,b⟩) both.1,both⟩
    · have both := W.1 (.inr b) c
      exact .inr ⟨V.2.1 (.inr ⟨a,b⟩) both.1,both⟩
  intro i il ih
  have old := go (i+1) (by omega) (by omega)
  have W := westWord H acy score hk (by omega : 4≤r+1) il rh (by omega)
  have V := westWord H acy score hk rl il (by omega) (by omega)
  rcases old with ⟨a,b,c⟩|⟨a,b,c⟩
  · have both := W.1 (.inl b) c
    exact ⟨V.2.1 (.inl ⟨a,b⟩) both.1,both⟩
  · have both := W.1 (.inr b) c
    exact ⟨V.2.1 (.inr ⟨a,b⟩) both.1,both⟩

omit one in
/-- Trace the upper 16 back to its creation in a column covered by
the incoming front. The first such 16 requires the adjacent 2→258.
The intervening strip is forced for however long the 16 persists. -/
theorem birth_or_entry {y x j : Nat} (yl : 4≤y) (xl : 6≤x) (yh : y+j+2≤K) (xh : x<K)
    (history : ∀ d≤j, t (y+d) x=73 ∨ t (y+d) x=9)
    (west : t (y+j) (x-1)=16) (here : t (y+j) x=73) :
    (∀ d≤j, t (y+d) (x-1)=16 ∧ t (y+d) x=73) ∨
    ∃ h<j, t (y+h) (x-2)=2 ∧ t (y+h+1) (x-2)=258 ∧ t (y+h) (x-1)=73 ∧
      ∀ d, h < d → d≤j → t (y+d) (x-1)=16 ∧ t (y+d) x=73 := by
  induction j with
  | zero =>
    left; intro d hd; obtain rfl : d=0 := by omega
    exact ⟨west,here⟩
  | succ j ih =>
    have S := (westWord H acy score hk (by omega : 4≤y+j) (by omega : 4≤x-1)
      (by omega) (by omega)).2.2.1
    rw [show x-1+1=x by omega] at S
    have e := S west here (history j (by omega))
    rcases e.2 with old|born
    · rcases ih (by omega) (fun d hd => history d (by omega)) old e.1 with entry|⟨h,lt,A,B,C,strip⟩
      · left; intro d lim; by_cases prev : d≤j
        · exact entry d prev
        · obtain rfl : d=j+1 := by omega
          exact ⟨west,here⟩
      refine .inr ⟨h,by omega,A,B,C,?_⟩
      intro d hd lim
      by_cases prev : d≤j
      · exact strip d hd prev
      · obtain rfl : d=j+1 := by omega
        exact ⟨west,here⟩
    · have W := (westWord H acy score hk (by omega : 4≤y+j) (by omega : 4≤x-2)
        (by omega) (by omega)).2.2.2
      rw [show x-2+1=x-1 by omega] at W
      have pair := W born west
      refine .inr ⟨j,by omega,pair.1,pair.2,born,?_⟩
      intro d hd lim
      obtain rfl : d=j+1 := by omega
      exact ⟨west,here⟩

omit one in
theorem birth {y x j : Nat} (yl : 4≤y) (xl : 6≤x) (yh : y+j+2≤K) (xh : x<K)
    (initial : t y (x-1)=73)
    (history : ∀ d≤j, t (y+d) x=73 ∨ t (y+d) x=9)
    (west : t (y+j) (x-1)=16) (here : t (y+j) x=73) :
    ∃ h<j, t (y+h) (x-2)=2 ∧ t (y+h+1) (x-2)=258 ∧ t (y+h) (x-1)=73 ∧
      ∀ d, h < d → d≤j → t (y+d) (x-1)=16 ∧ t (y+d) x=73 := by
  apply (birth_or_entry H acy score hk yl xl yh xh history west here).resolve_left
  intro all
  have e := (all 0 (by omega)).1
  change t y (x-1)=16 at e; omega

/-- A 129 one column inside the incoming plateau demands 16 on a
tile already known to be 73. At the leading column it forces 73 to
its east. Hence one descent costs at most one plain column. -/
theorem step_head {r a : Nat} (rl : 4≤r) (al : 5≤a) (rh : r+3≤K) (ah : a+4≤K)
    (plain : ∀ i, a ≤ i → i < K → t r i=73) (root : RootLine F v (K-1) r) :
    (t (r+1) a=9 ∨ t (r+1) a=16 ∨ t (r+1) a=129 ∨ t (r+1) a=73) ∧
    ∀ i, a+1 ≤ i → i < K → t (r+1) i=73 := by
  have R := tag_range (show r+2≤K by omega)
  have C := tag_range (show a+2≤K by omega)
  have T := test ⟨endTag K r-6,by omega⟩ ⟨endTag K a-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K a-6)=endTag K a by omega] at T
  have L : law (Strip.word t r a) := of_decide_eq_true (List.all_eq_true.mp T _
    (board_word H acy score hk rl (by omega) (by omega) (by omega)))
  have A := plain a le_rfl (by omega)
  have B := plain (a+1) (by omega) (by omega)
  have last := plain (K-1) (by omega) (by omega)
  have next := extend_line root (by rw [last]; decide) (.inl (by rw [last]; decide))
  have reg {c : Nat} (l : a ≤ c) (h : c+2≤K) (ed : edge₃ (t r c) (t (r+1) c)) := by
    have row : BandRow t r c K := by
      intro i lo hi; rw [plain i (by omega) (by omega),plain (i+1) (by omega) (by omega)]; decide
    exact rigid H acy one score hk (by omega) rh (by omega) h
      (across H acy score hk rl (by omega) (by omega) row ed).1 next
  have fromB (m : t (r+1) (a+1)=73) (i : Nat) (lo : a+1 ≤ i) (hi : i<K) : t (r+1) i=73 := by
    have ed : edge₃ (t r (a+1)) (t (r+1) (a+1)) := by rw [B,m]; decide
    rcases reg (by omega) (by omega) ed i lo hi with z|⟨eq,_⟩
    · exact z
    · exact eq ▸ m
  rcases L A B with ed|⟨m16,m⟩|hit|hit
  · have out := reg le_rfl (by omega) ed
    refine ⟨?_,?_⟩
    · rcases out a le_rfl (by omega) with z|⟨_,z⟩
      · exact .inr (.inr (.inr z))
      · exact .inl z
    · intro i lo hi
      rcases out i (by omega) hi with z|⟨eq,_⟩ <;> solve | exact z | omega
  · exact ⟨.inr (.inl m16),fromB m⟩
  · exact ⟨.inr (.inr (.inl hit)),fromB (Break129.forced_corner H acy one score hk rl al rh (by omega) plain hit root).1⟩
  · have impossible := (Break129.forced_corner H acy one score hk rl (by omega) rh (by omega)
        (fun c l h => plain c (by omega) h) hit root).2.2.1
    change t r a=16 at impossible
    omega

/-- Induction holds the eastern roots in place as long as the moving
left edge has not reached them. -/
theorem cone {y a f D : Nat} (yl : 4≤y) (al : 5≤a) (yh : y+D+2≤K)
    (space : a+D+3≤K) (buf : a+D≤f)
    (plain : ∀ i, a ≤ i → i < K → t y i=73)
    (roots : ∀ i, f ≤ i → i < K → RootLine F v i y) (ft : f<K) :
    ∀ j≤D, (∀ i, a+j ≤ i → i < K → t (y+j) i=73) ∧
      ∀ i, f ≤ i → i < K → RootLine F v i (y+j) := by
  intro j bound
  induction j with
  | zero => exact ⟨plain,roots⟩
  | succ j ih =>
    obtain ⟨top,lines⟩ := ih (by omega)
    refine ⟨(step_head (r:=y+j) (a:=a+j) H acy one score hk (by omega) (by omega) (by omega) (by omega) top
      (lines (K-1) (by omega) (by omega))).2,?_⟩
    intro i lo hi
    have m := top i (by omega) hi
    exact extend_line (y:=y+j) (lines i lo hi) (by rw [m]; decide) (.inl (by rw [m]; decide))
end
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.CornerCone
