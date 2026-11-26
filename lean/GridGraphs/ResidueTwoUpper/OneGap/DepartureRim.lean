import GridGraphs.ResidueTwoUpper.OneGap.DepartureTail

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Departure
open ResidueZero FanSlab BoundarySix.Connected SouthCap SouthCap.Strip
open SouthCap.Strip.GridScan SouthCap.Strip.GridScan.Rooted SouthCap.Strip.GridScan.Rooted.Buffered
private def rimLaw (w : Word) : Prop :=
  let (a,b,c,d) := w
  (a=9 → b=9 ∨ b=73) ∧ (a=73 → b=73) ∧ (a=72 → b=72 ∨ b=73) ∧
  ((a=2 ∨ a=3) → b=8 → d=3 ∨ d=7) ∧
  (a=8 → b=9 → d=3 ∨ d=7) ∧ (a=9 → b=73 → c≠7 ∧ c≠6 ∧ (c=2 → d=9 ∨ d=73)) ∧
  (a=8 → b=73 → c≠7 ∧ (c=3 → d=9 ∨ d=73)) ∧
  (a∈Port.shapes → b∈Port.shapes →
    (c∈Port.shapes → d=8 → c=2) ∧
    (c=8 → (b=72 ∨ b=73) ∧ (d=9 ∨ d=73)) ∧ (c=32 → b=9 ∧ (d=2 ∨ d=6)))
set_option synthInstance.maxSize 4096 in
private instance (w) : Decidable (rimLaw w) := by unfold rimLaw; infer_instance
private theorem checked : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (rimLaw w))=true := by native_decide
section
variable {u F v q} (H : PhysicalHalo u F v q (fanDirection u v)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
local notation "K" => (11+14*u)
local notation "t" => (tile F v)
include H acy score hk
private theorem ruleAt {r c} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K) :
    rimLaw (Strip.word t r c) := by
  have R := tag_range rh; have C := tag_range ch
  have T := checked ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at T
  exact of_decide_eq_true (List.all_eq_true.mp T _ (board_word H acy score hk rl cl rh ch))

theorem ray {r c n : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K)
    (z : n=9 ∨ n=72) (first : t r c=n ∨ t r c=73) :
    ∀ i, c ≤ i → i<K → t r i=n ∨ t r i=73 := by
  intro i l h
  induction i,l using Nat.le_induction with
  | base => exact first
  | succ i l ih =>
    have R := ruleAt H acy score hk rl (by omega : 4 ≤ i) rh (by omega)
    rcases ih (by omega) with m|m
    · rcases z with rfl|rfl
      · exact R.1 m
      · exact R.2.2.1 m
    · exact .inr (R.2.1 m)
include one
theorem plainBeyond {r c} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K)
    (first : t r c=9 ∨ t r c=73) (root : RootLine F v (K-1) r) :
    ∀ i, c < i → i<K → t r i=73 := by
  have masks := ray H acy score hk rl cl rh (.inl rfl) first
  have row : BandRow t r c K := by
    intro i l h
    apply physical_pair H acy score hk rl (by omega) rh h
    · rcases masks i l (by omega) with m|m <;> rw [m] <;> decide
    · rcases masks (i+1) (by omega) (by omega) with m|m <;> rw [m] <;> decide
  intro i l h
  rcases rigid H acy one score hk rl rh cl ch row root i (by omega) h with m|⟨e,_⟩ <;> solve | exact m | omega

theorem no28 {r x : Nat} (rl : 4≤r) (xl : 4≤x) (rh : r+3≤K) (xh : x+5≤K)
    (two : t r x=2 ∨ t r x=3) (eight : t r (x+1)=8) (east : t r (x+2)=9 ∨ t r (x+2)=73)
    (root : RootLine F v (K-1) r) : False := by
  have right := plainBeyond H acy one score hk rl (by omega) (by omega) (by omega) east root
  have last := right (K-1) (by omega) (by omega)
  have line := extend_line root (by rw [last]; decide) (.inl (by rw [last]; decide))
  have pin := (ruleAt H acy score hk rl xl (by omega) (by omega)).2.2.2.1 two eight
  have W := ruleAt H acy score hk rl (by omega : 4≤x+1) (by omega) (by omega)
  have tail (i : Nat) (l : x+2 ≤ i) (h : i+2≤K) : band (t r i) (t r (i+1)) := by
    rw [right (i+1) (by omega) (by omega)]
    by_cases e : i=x+2
    · subst i; rcases east with m|m <;> rw [m] <;> decide
    · rw [right _ (by omega) (by omega)]; decide
  rcases east with n|n
  · have low := W.2.2.2.2.1 eight n
    have adj := (ruleAt H acy score hk rl (by omega : 4≤x+2) (by omega) (by omega)).2.2.2.2.2.1 n
      (right _ (by omega) (by omega))
    have three := low.resolve_right adj.1
    have ed : edge₃ (t r (x+2)) (t (r+1) (x+2)) := by rw [n,three]; decide
    exact no_latch H acy one score hk (by omega) (by omega) (by omega) (by omega)
      (across H acy score hk rl (by omega) (by omega) tail ed).1 (.inl three) line
  · have res := W.2.2.2.2.2.2.1 eight n
    have three := pin.resolve_right res.1
    have m := res.2 three
    have ed : edge₃ (t r (x+2)) (t (r+1) (x+2)) := by rw [n]; rcases m with e|e <;> rw [e] <;> decide
    have rest := (across H acy score hk rl (by omega) (by omega) tail ed).1
    apply no_latch H acy one score hk (by omega) (by omega) (by omega) (by omega) _ (.inl three) line
    intro i l h
    by_cases e : i=x+1
    · subst i; rw [three]; rcases m with e|e <;> rw [e] <;> decide
    · exact rest i (by omega) h

/-- The two horizontal-parent candidates are impossible strictly inside
the read width while the preceding row retains its eastern north foot. -/
theorem no_sideways {r c} (rl : 4≤r) (cl : 5≤c) (rh : r+5≤K) (ch : c+6≤K)
    (nw : t r (c-1)∈Port.shapes) (n : t r c∈Port.shapes) (ne : t r (c+1)∈Port.shapes)
    (sw : t (r+1) (c-1)∈Port.shapes) (root : RootLine F v (K-1) r) :
    t (r+1) c≠8 ∧ t (r+1) c≠32 := by
  have L := (ruleAt H acy score hk rl (by omega : 4≤c-1) (by omega) (by omega)).2.2.2.2.2.2.2
  rw [show c-1+1=c by omega] at L
  have W := (ruleAt H acy score hk rl (by omega : 4≤c) (by omega) (by omega)).2.2.2.2.2.2.2 n ne
  constructor
  · intro bad
    have cap := (L nw n).1 sw bad
    obtain ⟨above,below⟩ := W.2.1 bad
    have last := ray H acy score hk rl (by omega) (by omega) (.inr rfl) above (K-1) (by omega) (by omega)
    have line := extend_line root (by rcases last with m|m <;> rw [m] <;> decide)
      (.inl (by rcases last with m|m <;> rw [m] <;> decide))
    apply no28 H acy one score hk (r:=r+1) (x:=c-1) (by omega) (by omega) (by omega) (by omega) (.inl cap) _ _ line
    · simpa only [show c-1+1=c by omega] using bad
    · simpa only [show c-1+2=c+1 by omega] using below
  · intro bad
    obtain ⟨above,d⟩ := W.2.2 bad
    have plain := plainBeyond H acy one score hk rl (by omega) (by omega) (by omega) (.inl above) root
    have last := plain (K-1) (by omega) (by omega)
    have line := extend_line root (by rw [last]; decide) (.inl (by rw [last]; decide))
    have edge := (ruleAt H acy score hk rl (by omega : 4≤c+1) (by omega) (by omega)).2.2.2.2.2.1 above
      (plain _ (by omega) (by omega))
    have two := d.resolve_right edge.2.1
    have after := edge.2.2 two
    have suffix := plainBeyond H acy one score hk (by omega) (by omega) (by omega) (by omega) after line
    have cap := after.resolve_left (fun z => CornerCone.no_end9 H acy one score hk
      (by omega) (by omega) (by omega) (by omega) (.inl two) z (fun i l h => suffix i (by omega) h) line)
    apply no_32_tail H acy one score hk (by omega) (by omega) (by omega) (by omega) bad two _ line
    intro i l h; rcases Nat.eq_or_lt_of_le l with rfl|lt
    · exact cap
    · exact suffix _ lt h

private def hazard (_a c : Nat) : Prop :=
  c=6 ∨ c=144 ∨ c=146 ∨ c=7 ∨ c=3 ∨ c=12 ∨ c=18 ∨ c=33
private instance (a c) : Decidable (hazard a c) := by unfold hazard; infer_instance
omit H acy one score hk in
private theorem only8 {a m : Nat} (L : m∈[3,6,7,8,12,18,32,144,146]) (N : ¬hazard a m) (E : m≠32) :
    m=8 := by simp at L; unfold hazard at N; tauto
private def eastLaw (w : Word) : Prop :=
  let (a,b,c,d) := w
  (a∈Port.shapes → b∈Port.shapes → hazard a c → hazard b d ∨ (c=144 ∧ d=129) ∨
    (c=3 ∧ (d=9 ∨ d=73 ∨ d=72 ∨ (d=8 ∧ b=128)))) ∧
  (a=129 → b=9 ∨ b=73) ∧ (a=144 → b=129 → d=18 ∨ d=146) ∧
  (a=129 → b=73 → c=128) ∧ (a=3 → b=72 → c=3 ∧ (d=9 ∨ d=73)) ∧
  (a=128 → b∈Port.shapes → c=8 → d=9 ∨ d=73) ∧
  (a∈Port.shapes → b∈Port.shapes → c=8 → a=128) ∧
  (b=128 → d=8 → c=2 ∨ c=3 ∨ ((a=48 ∨ a=56) ∧ c=a)) ∧
  (b∈Port.shapes → d=128 → c≠48 ∧ c≠56)
set_option synthInstance.maxSize 4096 in
private instance (w) : Decidable (eastLaw w) := by unfold eastLaw; infer_instance
omit H acy one score hk in
private theorem scan : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (eastLaw w))=true := by native_decide
omit one in
private theorem eastAt {r c} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K) :
    eastLaw (Strip.word t r c) := by
  have R := tag_range rh; have C := tag_range ch
  have T := scan ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at T
  exact of_decide_eq_true (List.all_eq_true.mp T _ (board_word H acy score hk rl cl rh ch))

private theorem no144129 {r c} (rl : 4≤r) (cl : 4≤c) (rh : r+3≤K) (ch : c+4≤K)
    (m : t r c=144) (n : t r (c+1)=129) (root : RootLine F v (K-1) r) : False := by
  have A := eastAt H acy score hk rl cl (by omega) (by omega)
  have B := eastAt H acy score hk rl (by omega : 4≤c+1) (by omega) (by omega)
  rcases B.2.1 n with nine|full
  · have tail := plainBeyond H acy one score hk rl (by omega) (by omega) (by omega) (.inl nine) root
    exact Break129.no_fast_tail H acy one score hk rl (by omega) (by omega) (by omega) n nine
      (fun i l h => tail i (by omega) h) root
  · have clash := A.2.2.1 m n; have other := B.2.2.2.1 n full
    change t (r+1) (c+1)=18 ∨ t (r+1) (c+1)=146 at clash
    change t (r+1) (c+1)=128 at other
    omega

private theorem no3end {r c} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+3≤K)
    (pin : t r c=3) (tail : t r (c+1)=9 ∨ t r (c+1)=73) (root : RootLine F v (K-1) r) : False := by
  have suffix := plainBeyond H acy one score hk rl (by omega) rh (by omega) tail root
  apply no_latch H acy one score hk rl (by omega) cl (by omega) _ (.inl pin) root
  intro i l h
  by_cases e : i=c
  · subst i; rw [pin]; rcases tail with m|m <;> rw [m] <;> decide
  rw [suffix (i+1) (by omega) (by omega)]
  by_cases e : i=c+1
  · subst i; rcases tail with m|m <;> rw [m] <;> decide
  · rw [suffix i (by omega) (by omega)]; decide

/-- Induct along columns, not fan depths. A 6 or 144 below a
straight interval would transmit a forbidden word to the following
column until reaching a plain eastern tooth. -/
private theorem no_hazard {r c e} (rl : 4≤r) (cl : 5≤c) (rh : r+6≤K) (eh : e+7≤K)
    (le : c≤e) (upper : ∀ i, c ≤ i → i < K → t r i∈Port.shapes)
    (tooth : t r e=73) (root : RootLine F v (K-1) r) : ¬hazard (t r c) (t (r+1) c) := by
  have top (i : Nat) (l : e ≤ i) (h : i<K) : t r i=73 := by
    induction i,l using Nat.le_induction with
    | base => exact tooth
    | succ i l ih => exact (ruleAt H acy score hk rl (by omega : 4 ≤ i) (by omega) (by omega)).2.1 (ih (by omega))
  have clean := (CornerCone.step_head H acy one score hk rl (by omega) (by omega) (by omega) top root).2
  have last := top (K-1) (by omega) (by omega)
  have line := extend_line root (by rw [last]; decide) (.inl (by rw [last]; decide))
  intro start
  have advance (i : Nat) (lo : c ≤ i) (hi : i≤e) (bad : hazard (t r i) (t (r+1) i)) :
      hazard (t r (i+1)) (t (r+1) (i+1)) := by
    have L := (eastAt H acy score hk rl (by omega : 4 ≤ i) (by omega) (by omega)).1
      (upper _ lo (by omega)) (upper _ (by omega) (by omega)) bad
    rcases L with keep|⟨m,n⟩|⟨pin,next⟩
    · exact keep
    · exact (no144129 H acy one score hk (by omega) (by omega) (by omega) (by omega) m n line).elim
    · exfalso
      rcases next with n|n|n|⟨n,up⟩
      · exact no3end H acy one score hk (by omega) (by omega) (by omega) (by omega) pin (.inl n) line
      · exact no3end H acy one score hk (by omega) (by omega) (by omega) (by omega) pin (.inr n) line
      · have P := (eastAt H acy score hk (by omega : 4≤r+1) (by omega : 4 ≤ i) (by omega) (by omega)).2.2.2.2.1 pin n
        have rim := ray H acy score hk (by omega : 4≤r+1) (by omega) (by omega) (n:=72) (.inr rfl) (.inl n)
          (K-1) (by omega) (by omega)
        have down := extend_line line (by rcases rim with m|m <;> rw [m] <;> decide)
          (.inl (by rcases rim with m|m <;> rw [m] <;> decide))
        exact no3end H acy one score hk (by omega) (by omega) (by omega) (by omega) P.1 P.2 down
      · have tail := (eastAt H acy score hk rl (by omega : 4 ≤ i+1) (by omega) (by omega)).2.2.2.2.2.1 up
          (upper (i+2) (by omega) (by omega)) n
        exact no28 H acy one score hk (by omega) (by omega) (by omega) (by omega) (.inr pin) n tail line
  have walk (i : Nat) (l : c ≤ i) (h : i≤e+1) : hazard (t r i) (t (r+1) i) := by
    induction i,l using Nat.le_induction with
    | base => exact start
    | succ i l ih => exact advance i l (by omega) (ih (by omega))
  have end' := walk (e+1) (by omega) le_rfl
  unfold hazard at end'
  rw [clean (e+1) le_rfl (by omega)] at end'
  omega

/-- A non-leading first departure needs a genuine opening on the
east: if the preceding read contains even one 73 and retains its
eastmost north foot, ALL interior departures are impossible. -/
theorem no_interior {r c e} (rl : 4≤r) (cl : 5≤c) (rh : r+6≤K) (eh : e+7≤K)
    (le : c≤e) (nw : t r (c-1)∈Port.shapes) (sw : t (r+1) (c-1)∈Port.shapes)
    (upper : ∀ i, c ≤ i → i < K → t r i∈Port.shapes) (tooth : t r e=73)
    (root : RootLine F v (K-1) r) : t (r+1) c∈Port.shapes := by
  by_contra bad
  have L := Departure.wordAt H acy score hk rl (by omega : 4≤c-1) (by omega) (by omega)
  change _ → t r (c-1+1)∈Port.shapes → _ ∧ (_ → t (r+1) (c-1+1)∉Port.shapes → _) at L
  rw [show c-1+1=c by omega] at L
  have cases := (L nw (upper _ le_rfl (by omega))).2 sw bad
  have S := no_sideways H acy one score hk rl cl (by omega) (by omega) nw
    (upper c le_rfl (by omega)) (upper (c+1) (by omega) (by omega)) sw root
  have N := no_hazard H acy one score hk rl cl rh eh le upper tooth root
  change t (r+1) c∈[6,8,32,144] at cases
  simp at cases
  rcases cases with z|z|z|z
  · exact N (.inl z)
  · exact S.1 z
  · exact S.2 z
  · exact N (.inr (.inl z))

/-- Even if the window does not read the column to its west, that
column has to carry the same nonstraight 48 or 56 on both rows. -/
theorem west_entry {r c e} (rl : 4≤r) (cl : 6≤c) (rh : r+6≤K) (eh : e+7≤K)
    (le : c≤e) (upper : ∀ i, c ≤ i → i < K → t r i∈Port.shapes) (tooth : t r e=73)
    (root : RootLine F v (K-1) r) (miss : t (r+1) c∉Port.shapes) :
    t (r+1) c=8 ∧ t r c=128 ∧ (t r (c-1)=48 ∨ t r (c-1)=56) ∧
      t (r+1) (c-1)=t r (c-1) ∧ (t r (c+1)=72 ∨ t r (c+1)=73) ∧
      (t (r+1) (c+1)=9 ∨ t (r+1) (c+1)=73) := by
  have n := upper c le_rfl (by omega)
  have ne := upper (c+1) (by omega) (by omega)
  have W := (ruleAt H acy score hk rl (by omega : 4≤c) (by omega) (by omega)).2.2.2.2.2.2.2 n ne
  have last := ray H acy score hk rl (by omega) (by omega) (n:=72) (.inr rfl) (.inr tooth)
    (K-1) (by omega) (by omega)
  have line := extend_line root (by rcases last with m|m <;> rw [m] <;> decide)
    (.inl (by rcases last with m|m <;> rw [m] <;> decide))
  have not32 : t (r+1) c≠32 := by
    intro bad
    obtain ⟨above,d⟩ := W.2.2 bad
    have plain := plainBeyond H acy one score hk rl (by omega) (by omega) (by omega) (.inl above) root
    have E := (ruleAt H acy score hk rl (by omega : 4≤c+1) (by omega) (by omega)).2.2.2.2.2.1 above
      (plain _ (by omega) (by omega))
    have two := d.resolve_right E.2.1
    have after := E.2.2 two
    have suffix := plainBeyond H acy one score hk (by omega) (by omega) (by omega) (by omega) after line
    have cap := after.resolve_left (fun z => CornerCone.no_end9 H acy one score hk
      (by omega) (by omega) (by omega) (by omega) (.inl two) z (fun i l h => suffix i (by omega) h) line)
    apply no_32_tail H acy one score hk (by omega) (by omega) (by omega) (by omega) bad two _ line
    intro i l h; rcases Nat.eq_or_lt_of_le l with rfl|lt
    · exact cap
    · exact suffix _ lt h
  have N := no_hazard H acy one score hk rl (by omega) rh eh le upper tooth root
  have cases := ((Departure.wordAt H acy score hk rl (by omega : 4≤c) (by omega) (by omega)) n ne).1 miss
  have eight := only8 (m:=t (r+1) c) cases N not32
  obtain ⟨up,down⟩ := W.2.1 eight
  have parent := (eastAt H acy score hk rl (by omega : 4≤c) (by omega) (by omega)).2.2.2.2.2.2.1 n ne eight
  have west := (eastAt H acy score hk rl (by omega : 4≤c-1) (by omega) (by omega)).2.2.2.2.2.2.2.1
  rw [show c-1+1=c by omega] at west
  have no (m : t (r+1) (c-1)=2 ∨ t (r+1) (c-1)=3) : False :=
    no28 H acy one score hk (r:=r+1) (x:=c-1) (by omega) (by omega) (by omega) (by omega)
      m (by simpa only [show c-1+1=c by omega] using eight)
      (by simpa only [show c-1+2=c+1 by omega] using down) line
  rcases west parent eight with m|m|pair
  · exact (no (.inl m)).elim
  · exact (no (.inr m)).elim
  · exact ⟨eight,parent,pair.1,pair.2,up,down⟩

def WestArrival {u F} (Q : Flow (n:=N u) F) (v : L7.View) (y x j i : Nat) :=
  i=0 ∧ (tile F v (y+j) x=8 ∧ tile F v (y+(j-1)) x=128 ∧
      (tile F v (y+j) (x-1)=48 ∨ tile F v (y+j) (x-1)=56) ∧
      tile F v (y+j) (x-1)=tile F v (y+(j-1)) (x-1)) ∧ WestExit Q v (y+j) x

set_option maxHeartbeats 650000 in
theorem covered {y x W h j i} (Q : Flow F) (price : Prices F v)
    (yl : 4≤y) (xl : 7≤x) (hr : y+h+8≤K) (wc : x+W+7≤K) (bad : First F v y x W h j i)
    (tip : t (y+(j-1)) (x+W)=73) (line : RootLine F v (K-1) (y+(j-1))) :
    WestArrival Q v y x j i := by
  obtain ⟨jl,jh,iw,miss,up,early⟩ := bad
  let r := y+(j-1)
  have height : r+1=y+j := by dsimp [r]; omega
  have upper (c : Nat) (l : x+i ≤ c) (h : c<K) : t r c∈Port.shapes := by
    by_cases inside : c≤x+W
    · simpa only [show x+(c-x)=c by omega] using up (j-1) (by omega) (c-x) (by omega)
    · have ray' := plainBeyond H acy one score hk (by dsimp [r]; omega : 4≤r) (by omega : 4≤x+W)
        (by dsimp [r]; omega) (by omega) (.inr tip) line c (by omega) h
      rw [ray']; decide
  have out := west_entry H acy one score hk (by dsimp [r]; omega : 4≤r) (by omega : 6≤x+i)
    (by dsimp [r]; omega) (by omega) (by omega) upper tip line (by rwa [height])
  obtain ⟨m,a,w,eq,b,n⟩ := out
  have zero : i=0 := by
    by_contra nz
    have ok := early (i-1) (by omega)
    change t (y+j) (x+(i-1))∈Port.shapes at ok
    rw [←height,show x+(i-1)=x+i-1 by omega,eq] at ok
    have reject {m : Nat} (p : m=48 ∨ m=56) : m∉Port.shapes := by rcases p with rfl|rfl <;> decide
    exact reject w ok
  subst i; simp only [Nat.add_zero] at m a w eq b n
  have ow := west_owners Q price (by dsimp [r]; omega) (by omega) (by dsimp [r]; omega) (by omega) m a w eq b n
  refine ⟨rfl,⟨height ▸ m,a,?_,height ▸ eq⟩,height ▸ ow⟩
  rw [←height,eq]; exact w

/-- The arithmetic test suffices to provide both the upper 73 and
the actual north foot. There is no flatness assumption on previous
movement windows in this test. -/
theorem covered_of_budget {y f x W h j i} (Q : Flow F) (price : Prices F v)
    (front : Front F v q K y f) (left : f≤x) (yl : 4≤y) (fl : 7≤f)
    (hr : y+h+8≤K) (wc : x+W+8≤K) (feet : q+2≤K) (bad : First F v y x W h j i)
    (budget : f+3*((j-1)/4)+(j-1)%4≤x+W) : WestArrival Q v y x j i := by
  let z := j-1
  have jh := bad.2.1
  have mid := CornerCone.blocks H acy one score hk (y:=y) (a:=f) (s:=z/4) (f:=K-1)
    yl (by omega) (by dsimp [z]; omega) (by dsimp [z]; omega) (by dsimp [z]; omega)
    (by omega) (front.1 y le_rfl le_rfl) (fun i l h => front.2.2 i (by omega) h (by omega))
  have tail := CornerCone.cone H acy one score hk (D:=z%4)
    (by omega) (by omega) (by dsimp [z]; omega) (by dsimp [z]; omega) (by dsimp [z]; omega)
    mid.1 mid.2 (by omega) (z%4) le_rfl
  rw [show y+4*(z/4)+z%4=y+(j-1) by dsimp [z]; omega] at tail
  exact covered H acy one score hk Q price yl (by omega) hr (by omega) bad
    (tail.1 (x+W) budget (by omega)) (tail.2 (K-1) le_rfl (by omega))

omit one in
/-- A locally priced leading 8 is not a *first* departure: the
western feed of its 128 already required a nonstraight mask in
the read column one row earlier. -/
theorem impossible_arrival {y x f W h j i} (Q : Flow F)
    (front : Front F v q K y f) (left : f≤x) (yl : 4≤y) (xl : 6≤x) (wc : x+W+4≤K)
    (hr : y+h+3≤K) (bad : First F v y x W h j i) (arrival : WestArrival Q v y x j i) : False := by
  obtain ⟨rfl,⟨_,cap,west,same⟩,_⟩ := arrival
  obtain ⟨jl,jh,_,_,up,_⟩ := bad
  have prev : 2≤j := by
    by_contra! lt
    have m := front.1 y le_rfl le_rfl x left (by omega)
    change t y x=73 at m
    rw [show y+(j-1)=y by omega] at cap
    omega
  have L := (eastAt H acy score hk (by omega : 4≤y+(j-2)) (by omega : 4≤x-1) (by omega) (by omega)).2.2.2.2.2.2.2.2
  rw [show x-1+1=x by omega,show y+(j-2)+1=y+(j-1) by omega] at L
  have no := L (up (j-2) (by omega) 0 (by omega)) cap
  rw [same] at west
  exact west.elim no.1 no.2

/-- A physical window can be widened before finding its first bad
tile. The cone therefore need not end inside the original read. -/
theorem straight_of_room {y f x W h} (Q : Flow F) (price : Prices F v)
    (front : Front F v q K y f) (left : f≤x) (yl : 4≤y) (fl : 7≤f)
    (ht : y+h+8≤K) (wc : x+W+8≤K) (space : f+3*((h-1)/4)+(h-1)%4+8≤K)
    (feet : q+2≤K) : Straight F v y x W h := by
  -- The tooth and foot used to exclude row j both live on row j-1.
  let W' := max W (f+3*((h-1)/4)+(h-1)%4-x)
  have width : x+W'+8≤K := by dsimp [W']; omega
  suffices all : Straight F v y x W' h from fun j jh i ih => all j jh i (by dsimp [W']; omega)
  by_contra neg
  obtain ⟨j,i,bad⟩ := first_of_bad front left (by omega) neg
  have upper := bad.2.1
  have monotone (a b : Nat) (ab : a≤b) : 3*(a/4)+a%4≤3*(b/4)+b%4 := by omega
  have budget := monotone (j-1) (h-1) (by omega)
  have entry := covered_of_budget H acy one score hk Q price front left yl fl ht width feet bad (by dsimp [W']; omega)
  exact impossible_arrival H acy score hk Q front left yl (by omega) (by omega) (by omega) bad entry
end
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Departure
