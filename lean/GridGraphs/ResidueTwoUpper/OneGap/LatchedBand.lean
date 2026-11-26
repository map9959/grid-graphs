import GridGraphs.ResidueTwoUpper.OneGap.BufferedSuffix

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.Buffered
open ResidueZero L7 FanSlab BoundarySix.Connected

def BandRow (t : Tiles) (r a k : Nat) := ∀ i, a ≤ i → i+2≤k → band (t r i) (t r (i+1))=true
private def latch (a : Nat) : Prop := a=3 ∨ a=7
private instance (a : Nat) : Decidable (latch a) := by unfold latch; infer_instance
private def law (w : Word) : Prop :=
  let (a,b,c,d) := w
  band a b →
    (latch a → latch c ∧ edge₃ a c) ∧
    (edge₃ a c → band c d ∧ edge₃ b d) ∧
    (a=9 → b=9 → latch d ∧ edge₃ b d)
private instance (w : Word) : Decidable (law w) := by unfold law; infer_instance
private theorem verified : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (law w))=true := by native_decide

private theorem edgeHead {a b} (h : edge₃ a b=true) : bit b 0=1 := by
  simp [edge₃] at h
  rcases h with h|h|h|h|h|h|h <;> rw [h.2] <;> decide

def bandMask (a : Nat) := [3,7,9,73].contains a
theorem band_left_mask {a b} (h : band a b=true) : bandMask a=true := by
  simp [band] at h
  rcases h with h|h|h|h|h|h|h <;> rw [h.1] <;> decide

private def maskTest (w : Word) := !(bandMask w.1 && bandMask w.2.1) || band w.1 w.2.1
private theorem maskCheck : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all maskTest=true := by native_decide

private theorem ends {a b} (p : band a b=true) (n : ¬latch a) :
    (a=9 ∨ a=73) ∧ ((a=9 → b=9 → False) → b=73) := by
  simp [band] at p
  unfold latch at n
  grind

section
variable {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
  (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
  (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
local notation "K" => (11+14*u)
local notation "t" => (tile F v)
include H acy score hk

theorem physical_pair {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K)
    (a : bandMask (t r c)) (b : bandMask (t r (c+1))) : band (t r c) (t r (c+1)) := by
  have m := board_word H acy score hk rl cl rh ch
  have R := tag_range rh
  have C := tag_range ch
  have test := maskCheck ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at test
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at test
  simpa only [maskTest,word,a,b,Bool.true_and,Bool.not_true,Bool.false_or] using List.all_eq_true.mp test _ m

private theorem physicalLaw {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K) :
    law (word t r c) := by
  have m := board_word H acy score hk rl cl rh ch
  have R := tag_range rh
  have C := tag_range ch
  have test := verified ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at test
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at test
  exact of_decide_eq_true (List.all_eq_true.mp test _ m)

-- A stable vertical edge propagates horizontally through an entire band.
theorem across {r a} (rl : 4≤r) (al : 4≤a) (rh : r+2≤K)
    (row : BandRow t r a K) (start : edge₃ (t r a) (t (r+1) a)) :
    BandRow t (r+1) a K ∧ ∀ i, a ≤ i → i<K → edge₃ (t r i) (t (r+1) i) := by
  have edges (i : Nat) (lo : a ≤ i) (hi : i<K) : edge₃ (t r i) (t (r+1) i) := by
    induction i,lo using Nat.le_induction with
    | base => exact start
    | succ i il ih =>
      exact ((physicalLaw H acy score hk rl (by omega) rh (by omega) (row i il (by omega))).2.1
        (ih (by omega))).2
  refine ⟨?_,edges⟩
  intro i il ih
  exact ((physicalLaw H acy score hk rl (by omega) rh ih (row i il ih)).2.1
    (edges i il (by omega))).1

omit H acy score hk in
private theorem tipBits {a b : Nat} (p : band a b=true) :
    bit b 0=1 ∧ (bit b 1=1 ∨ bit b 3=1) := by
  simp [band] at p
  rcases p with h|h|h|h|h|h|h <;> obtain ⟨_,rfl⟩ := h <;> decide

include one
omit score in
private theorem eastNo {y} (lo : 1≤y) (hi : y<K) (root : RootLine F v (K-1) y) :
    bit (t y (K-1)) 1 ≠ 1 := by
  rw [show K-1=10+14*u by omega] at *
  exact no_east_middle H acy one lo hi root

/-- No aspect ratio and no supply of western columns: a 3 or 7 at
the start of an admitted suffix reproduces the band at the same
column all the way to the south rim. A single retained north foot
at the east edge is enough for a contradiction. -/
theorem no_latch {y a : Nat} (yl : 4≤y) (yh : y<K) (al : 4≤a) (ah : a+2≤K)
    (row : BandRow t y a K) (anchor : t y a=3 ∨ t y a=7)
    (root : RootLine F v (K-1) y) : False := by
  have persist (r : Nat) (lo : y≤r) (hi : r<K) :
      BandRow t r a K ∧ latch (t r a) ∧ RootLine F v (K-1) r := by
    induction r,lo using Nat.le_induction with
    | base => exact ⟨row,anchor,root⟩
    | succ r lr ih =>
      obtain ⟨old,pin,line⟩ := ih (by omega)
      have ⟨lower,edge⟩ := (physicalLaw H acy score hk (by omega) al (by omega) ah (old a le_rfl ah)).1 pin
      have new := (across H acy score hk (by omega) al (by omega) old edge).1
      have last (j) (b : BandRow t j a K) := tipBits (b (K-2) (by omega) (by omega))
      have m := last r old
      have n := last (r+1) new
      rw [show K-2+1=K-1 by omega] at m n
      have east := eastNo H acy one hk (by omega : 1≤r) (by omega : r<K) line
      exact ⟨new,lower,extend_line line (m.2.resolve_left east) (.inr n.1)⟩
  obtain ⟨endRow,_,line⟩ := persist (K-1) (by omega) (by omega)
  have p := tipBits (endRow (K-2) (by omega) (by omega))
  rw [show K-2+1=K-1 by omega] at p
  rw [show K-1=10+14*u by omega] at p line
  exact p.2.elim (no_east_middle H acy one (by omega) (by omega) line)
    (no_south_middle H acy one (by omega) (by omega) line)

/-- Any band ending at a rooted eastern tile is already a straight
suffix, except possibly for a single 9 on its westernmost tile. -/
theorem rigid {y a : Nat} (yl : 4≤y) (yh : y+2≤K) (al : 4≤a) (ah : a+2≤K)
    (row : BandRow t y a K) (root : RootLine F v (K-1) y) :
    ∀ i, a ≤ i → i<K → t y i=73 ∨ i=a ∧ t y i=9 := by
  have no (i : Nat) (il : a ≤ i) (ih : i<K) : ¬latch (t y i) := by
    intro h
    by_cases end' : i=K-1
    · subst i
      have z := eastNo H acy one hk (by omega : 1≤y) (by omega : y<K) root
      rcases h with m|m <;> apply z <;> rw [m] <;> decide
    · exact no_latch H acy one score hk yl (by omega) (by omega) (by omega)
        (fun j jl jh => row j (by omega) jh) h root
  have no99 (i : Nat) (il : a ≤ i) (ih : i+2≤K) (m : t y i=9) (n : t y (i+1)=9) : False := by
    have ⟨pin,edge⟩ := (physicalLaw H acy score hk yl (by omega) yh ih (row i il ih)).2.2 m n
    have next := across H acy score hk yl (a:=i+1) (by omega) yh (fun j l h => row j (by omega) h) edge
    have endEdge := next.2 (K-1) (by omega) (by omega)
    have upper := tipBits (row (K-2) (by omega) (by omega))
    rw [show K-2+1=K-1 by omega] at upper
    have east := eastNo H acy one hk (by omega : 1≤y) (by omega : y<K) root
    have head : bit (t (y+1) (K-1)) 0=1 := by
      exact edgeHead endEdge
    have line := extend_line root (upper.2.resolve_left east) (.inr head)
    by_cases last : i+1=K-1
    · rw [last] at pin
      have z := eastNo H acy one hk (by omega : 1≤y+1) (by omega : y+1<K) line
      rcases pin with m|m <;> apply z <;> rw [m] <;> decide
    · exact no_latch H acy one score hk (by omega) (by omega) (by omega) (by omega)
        next.1 pin line
  intro i il ih
  by_cases first : i=a
  · subst i
    have p := row a le_rfl ah; have n := no a le_rfl (by omega)
    exact ((ends p n).1.elim (fun h => .inr ⟨rfl,h⟩) Or.inl)
  · have p := row (i-1) (by omega) (by omega)
    have z := no99 (i-1) (by omega) (by omega)
    have n := no (i-1) (by omega) (by omega)
    simp only [show i-1+1=i by omega] at p z
    exact .inl ((ends p n).2 z)

end

/-- Refine three consecutive 73-pairs below a plain seed: the first
step into the band costs just two columns. -/
private def plainRule (w : Word) : Prop :=
  let (a,b,c,d) := w
  a=73 → b=73 → (d=9 ∨ d=73 ∨ d=129) ∧
    ((c=9 ∨ c=73 ∨ c=129) → d=9 ∨ d=73) ∧ ((c=9 ∨ c=73) → band c d)
private instance (w : Word) : Decidable (plainRule w) := by unfold plainRule; infer_instance
private theorem plainCheck : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (plainRule w))=true := by native_decide

theorem mixed_end {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y a f D : Nat} (yl : 4≤y) (al : 4≤a) (height : y+D+2≤11+14*u)
    (width : f+2≤11+14*u) (af : a≤f) (budget : a+3*D≤f+1)
    (plain : ∀ i, a ≤ i → i<11+14*u → tile F v y i=73)
    (root : ∀ i, f ≤ i → i<11+14*u → RootLine F v i y) :
    ∀ j≤D, ∀ i, f ≤ i → i<11+14*u →
      (tile F v (y+j) i=73 ∨ i=f ∧ tile F v (y+j) i=9) ∧ RootLine F v i (y+j) := by
  let k := 11+14*u
  let t := tile F v
  have ruleAt (c : Nat) (cl : a ≤ c) (ch : c+2≤k) := by
    have m := board_word H acy score hk yl (by omega : 4≤c) (by omega) ch
    have rh : y+2≤k := by dsimp [k]; omega
    have R := tag_range rh; have C := tag_range ch
    have test := plainCheck ⟨endTag k y-6,by omega⟩ ⟨endTag k c-6,by omega⟩
    dsimp only at test
    rw [show 6+(endTag k y-6)=endTag k y by omega,show 6+(endTag k c-6)=endTag k c by omega] at test
    exact (of_decide_eq_true (List.all_eq_true.mp test _ m) : plainRule (word t y c))
      (plain c cl (by dsimp [k] at ch; omega)) (plain (c+1) (by omega) (by dsimp [k] at ch; omega))
  have first : BandRow t (y+1) (a+2) k := by
    intro i il ih
    have e := (ruleAt (i-2) (by omega) (by omega)).1
    have h := (ruleAt (i-1) (by omega) (by omega)).2.1
    simp only [show i-2+1=i-1 by omega] at e
    simp only [show i-1+1=i by omega] at h
    exact (ruleAt i (by omega) ih).2.2 (h e)
  intro j
  induction j with
  | zero => exact fun _ i l h => ⟨.inl (plain i (by omega) h),root i l h⟩
  | succ j ih =>
    intro bound
    have tail : BandRow t (y+(j+1)) f k := by
      intro i l h
      simpa only [show y+1+j=y+(j+1) by omega] using
        bands_below_from H acy score hk (D:=j) (by omega : 4≤y+1) (by omega : 4≤a+2)
          (by omega) first j le_rfl i (by omega) h
    have heads (i : Nat) (l : f ≤ i) (h : i<k) : bit (t (y+(j+1)) i) 0=1 := by
      by_cases e : i=k-1
      · subst i
        have p := tipBits (tail (k-2) (by dsimp [k]; omega) (by omega))
        rw [show k-2+1=k-1 by omega] at p
        exact p.1
      · have p := band_left_mask (tail i l (by omega))
        have head {m} (p : bandMask m=true) : bit m 0=1 := by
          simp [bandMask] at p
          rcases p with rfl|rfl|rfl|rfl <;> decide
        exact head p
    have lines (i : Nat) (l : f ≤ i) (h : i<k) : RootLine F v i (y+(j+1)) := by
      obtain ⟨m,line⟩ := ih (by omega) i l h
      apply extend_line (y:=y+j) line _ (.inr (heads i l h))
      rcases m with m|⟨_,m⟩ <;> rw [m] <;> decide
    have reg := rigid H acy one score hk (by omega : 4≤y+(j+1)) (by omega) (by omega : 4≤f)
      width tail (lines (k-1) (by dsimp [k]; omega) (by omega))
    exact fun i l h => ⟨reg i l h,lines i l h⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.Buffered
