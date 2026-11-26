import GridGraphs.ResidueTwoUpper.OneGap.MixedRimWave

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.Buffered
open ResidueZero L7 FanSlab BoundarySix.Connected

def band (a b : Nat) := [(3,9),(3,73),(7,3),(7,7),(9,9),(9,73),(73,73)].contains (a,b)
def edge₃ (a c : Nat) := [(3,3),(3,7),(7,7),(9,3),(9,7),(73,9),(73,73)].contains (a,c)
private def edge₂ (a c : Nat) := edge₃ a c || (a==73 && c==129)
private def edge₁ (a c : Nat) := edge₂ a c || (a==73 && c==144)
private def join (a c : Nat) : Prop := bit a 3=1 ∧ (bit a 6=1 ∨ bit c 0=1)
private instance (a c : Nat) : Decidable (join a c) := by unfold join; infer_instance
private def rule (w : Word) : Prop :=
  let (a,b,c,d) := w
  band a b → edge₁ b d ∧ (edge₁ a c → edge₂ b d) ∧
    (edge₂ a c → edge₃ b d) ∧ (edge₃ a c → band c d) ∧
    (band c d → (bit a 1=1 ∧ bit b 0=1) ∨
      (join a c ∧ join b d ∧ bit c 1=1 ∧ bit d 0=1) ∨ a=73)
private instance (w : Word) : Decidable (rule w) := by unfold rule; infer_instance
private theorem checked : ∀ a b : Fin 7, (bankWords (6+a.val) (6+b.val)).all
    (fun w => decide (rule w))=true := by native_decide

private theorem physical_rule {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {r c : Nat} (rl : 4≤r) (rh : r+2≤11+14*u) (cl : 4≤c) (ch : c+2≤11+14*u) :
    rule (word (tile F v) r c) := by
  let k := 11+14*u
  change r+2≤k at rh
  change c+2≤k at ch
  have m := board_word H acy score hk rl cl rh ch
  have R := tag_range rh
  have C := tag_range ch
  have test := checked ⟨endTag k r-6,by omega⟩ ⟨endTag k c-6,by omega⟩
  dsimp only at test
  rw [show 6+(endTag k r-6)=endTag k r by omega,show 6+(endTag k c-6)=endTag k c by omega] at test
  exact of_decide_eq_true (List.all_eq_true.mp test _ m)

theorem bands_below_from {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y a D : Nat} (yl : 4≤y) (al : 4≤a) (height : y+D+1≤11+14*u)
    (initial : ∀ i, a ≤ i → i+2≤11+14*u → band (tile F v y i) (tile F v y (i+1))) :
    ∀ j≤D, ∀ i, a+3*j ≤ i → i+2≤11+14*u →
      band (tile F v (y+j) i) (tile F v (y+j) (i+1)) := by
  let k := 11+14*u
  let t := tile F v
  have localRule (r c : Nat) (rl : y≤r) (rh : r+2≤k) (cl : a≤c) (ch : c+2≤k) :
      rule (word t r c) := physical_rule H acy score hk (by omega) rh (by omega) ch
  intro j bound i lo hi
  change band (t (y+j) i) (t (y+j) (i+1))=true
  exact (by
    induction j generalizing i with
    | zero => exact initial i (by omega) hi
    | succ j ih =>
      have useRule (c : Nat) (l : a+3*j ≤ c) (h : c+2≤k) :=
        localRule (y+j) c (by omega) (by dsimp [k] at *; omega) (by omega) h (ih (by omega) c l h)
      have e₁ := (useRule (i-3) (by omega) (by omega)).1
      have e₂ := (useRule (i-2) (by omega) (by omega)).2.1
      have e₃ := (useRule (i-1) (by omega) (by omega)).2.2.1
      have out := (useRule i (by omega) hi).2.2.2.1
      simp only [show i-3+1=i-2 by omega] at e₁
      simp only [show i-2+1=i-1 by omega] at e₂
      simp only [show i-1+1=i by omega] at e₃
      exact out (e₃ (e₂ e₁)))

theorem bands_below {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (_one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y a D : Nat} (yl : 4≤y) (al : 4≤a) (height : y+D+1≤11+14*u)
    (plain : ∀ i, a ≤ i → i<11+14*u → tile F v y i=73) :
    ∀ j≤D, ∀ i, a+3*j ≤ i → i+2≤11+14*u →
      band (tile F v (y+j) i) (tile F v (y+j) (i+1)) :=
  bands_below_from H acy score hk yl al height (fun i lo hi => by
    rw [plain i lo (by omega),plain (i+1) (by omega) (by omega)]; decide)

/-- `a..f` is a buffer of ordinary plateau tiles, *not* assumed rooted.
Each lower row loses at most three columns of the pair alphabet on the
west. North roots keep their original columns. One lookahead row of
the alphabet prevents a 9 from ending a rooted column. -/
theorem propagate {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y a f D : Nat} (yl : 4≤y) (al : 4≤a) (height : y+D+3≤11+14*u)
    (width : f+2≤11+14*u) (budget : a+3*(D+1)≤f)
    (plain : ∀ i, a ≤ i → i<11+14*u → tile F v y i=73)
    (root : ∀ i, f ≤ i → i<11+14*u → RootLine F v i y) :
    ∀ j≤D, ∀ i, f ≤ i → i<11+14*u →
      tile F v (y+j) i=73 ∧ RootLine F v i (y+j) := by
  let k := 11+14*u
  let t := tile F v
  have localRule (r c : Nat) (rl : y≤r) (rh : r+2≤k) (cl : a≤c) (ch : c+2≤k) :
      rule (word t r c) := physical_rule H acy score hk (by omega) rh (by omega) ch
  have bands := bands_below H acy one score hk (D:=D+1) yl al (by omega) plain
  intro j
  induction j with
  | zero => exact fun _ i l h => ⟨plain i (by omega) h,root i l h⟩
  | succ j ih =>
    intro bound
    let r := y+(j+1)
    have roots (c : Nat) (cl : f ≤ c) (ch : c<k) : RootLine F v c r := by
      obtain ⟨m,path⟩ := ih (by omega) c cl ch
      exact extend_line (y:=y+j) path (by rw [m]; decide) (.inl (by rw [m]; decide))
    have top := bands (j+1) (by omega) f (by omega) width
    have bot := bands (j+2) (by omega) f (by omega) width
    have choices := (localRule r f (by dsimp [r]; omega) (by dsimp [r,k] at *; omega)
      (by omega) width top).2.2.2.2 bot
    have l := roots f le_rfl (by dsimp [k]; omega)
    have h := roots (f+1) (by omega) (by dsimp [k]; omega)
    have m : t r f=73 := by
      rcases choices with ⟨arm,head⟩|⟨⟨m₁,z₁⟩,⟨m₂,z₂⟩,arm,head⟩|ok
      · exact (no_crossbar acy one (by dsimp [r]; omega) (by omega) l h arm head).elim
      · exact (no_crossbar acy one (by dsimp [r]; omega) (by omega)
          (extend_line l m₁ z₁) (extend_line h m₂ z₂) arm head).elim
      · exact ok
    intro i lo hi
    refine ⟨?_,roots i lo hi⟩
    change t r i=73
    induction i,lo using Nat.le_induction with
    | base => exact m
    | succ i l ih =>
      have p := bands (j+1) (by omega) i (by omega) (by omega)
      change band (t r i) (t r (i+1))=true at p
      rw [ih (by omega)] at p
      simpa [band] using p

/-- Reach the rectangle at any depth paid for by the plain western
buffer. No intermediate `Front`, straightness or owner scan is an input. -/
theorem exclude_at {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y a f D : Nat} (front : Front F v q (11+14*u) y a)
    (yl : 4≤y) (al : 4≤a) (feet : q<f)
    (height : y+D+8≤11+14*u) (width : f+8≤11+14*u) (budget : a+3*(D+1)≤f)
    (slope : 3*(11+14*u-(y+D))≤4*(11+14*u-f)) : False := by
  have atEnd := propagate H acy one score hk yl al (by omega) (by omega) budget
    (fun i l h => front.1 _ le_rfl le_rfl i l h)
    (fun i l h => front.2.2 _ (by omega) h (by omega)) D le_rfl
  apply Mixed.exclude_suffix H acy one score hk (y+D) f (by omega) (by omega)
    height width slope
  intro i l h
  exact ⟨.inl (atEnd i l h).1,(atEnd i l h).2⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.Buffered
