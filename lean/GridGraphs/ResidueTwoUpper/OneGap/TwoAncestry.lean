import GridGraphs.ResidueTwoUpper.OneGap.CornerCone

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.TwoAncestry
open ResidueZero L7 FanSeed FanSlab BoundarySix.Connected SouthCap SouthCap.Strip
open SouthCap.Strip.GridScan SouthCap.Strip.GridScan.Rooted

-- Projections onto individual plaquettes: no scan of pairs of banks is needed.
private def law (w : Word) : Prop :=
  let (a,b,c,d) := w
  (b=2 → d=258 → a=288 ∨ a=292) ∧
  (c=288 → d=2 → ((a=128 ∨ a=192) ∧ (b=8 ∨ b=9)) ∨ (a=144 ∧ b=144) ∨ (a=146 ∧ b=146)) ∧
  (c=292 → d=2 → (a=288 ∨ a=292) ∧ (b=2 ∨ b=32 ∨ b=36)) ∧
  (c=2 → d=73 → (a=2 ∨ a=8 ∨ a=9) ∧ (b=72 ∨ b=73)) ∧
  (c=2 → d=72 → ((a=32 ∨ a=36) ∧ (b=128 ∨ b=384)) ∨
    (a=144 ∧ b=144) ∨ (a=146 ∧ b=146)) ∧
  (c=16 → d=73 → a=16 ∨ a=18 ∨ a=73) ∧ (b=73 → d=16 → a=2 ∧ c=258) ∧
  ((b=9 ∨ b=73) → a≠144 ∧ a≠146 ∧ a≠384)
set_option synthInstance.maxSize 4096 in
private instance (w) : Decidable (law w) := by unfold law; infer_instance
private theorem check : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (law w))=true := by native_decide

private def returnLaw (w : Word) : Prop :=
  let (a,b,c,d) := w
  (((b=9 ∨ b=73) → (d=9 ∨ d=73) →
    (c=192 → a=192) ∧ (c=128 → a=128 ∨ a=129 ∨ a=192))) ∧
  (b=128 → d=128 → a=292 ∧ (c=36 ∨ c=292)) ∧
  (b=129 → d=128 → c=292) ∧ (b=36 → d=2 → a=292)
set_option synthInstance.maxSize 4096 in
private instance (w) : Decidable (returnLaw w) := by unfold returnLaw; infer_instance
private theorem returnCheck : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (returnLaw w))=true := by native_decide

def Run (l m r : Nat) : Prop := (l=288 ∨ l=292) ∧ m=2 ∧ (r=72 ∨ r=73)
def Source (l m r : Nat) : Prop :=
  ((l=128 ∨ l=192) ∧ (m=8 ∨ m=9) ∧ (r=72 ∨ r=73)) ∨
  ((l=288 ∨ l=292) ∧ (m=32 ∨ m=36) ∧ (r=128 ∨ r=384)) ∨
  (l=144 ∧ m=144 ∧ r=144) ∨ (l=146 ∧ m=146 ∧ r=146)

private theorem backward {a b c d e f : Nat} (L : law (a,b,d,e)) (R : law (b,c,e,f))
    (row : Run d e f) : Run a b c ∨ Source a b c := by
  obtain ⟨dl,rfl,fr⟩ := row
  have A := L.2.1; have B := L.2.2.1
  have C := R.2.2.2.1; have D := R.2.2.2.2.1
  unfold Run Source
  rcases dl with rfl|rfl <;> rcases fr with rfl|rfl <;> grind

section
variable {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
local notation "K" => (11+14*u)
local notation "t" => (Rooted.tile F v)
include H acy score hk
private theorem wordAt {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K) :
    law (Strip.word t r c) := by
  have R := tag_range rh; have C := tag_range ch
  have T := check ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at T
  exact of_decide_eq_true (List.all_eq_true.mp T _ (board_word H acy score hk rl cl rh ch))

private theorem returnAt {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+2≤K) :
    returnLaw (Strip.word t r c) := by
  have R := tag_range rh; have C := tag_range ch
  have T := returnCheck ⟨endTag K r-6,by omega⟩ ⟨endTag K c-6,by omega⟩
  dsimp only at T
  rw [show 6+(endTag K r-6)=endTag K r by omega,show 6+(endTag K c-6)=endTag K c by omega] at T
  exact of_decide_eq_true (List.all_eq_true.mp T _ (board_word H acy score hk rl cl rh ch))

private theorem before128 {r c : Nat} (rl : 4≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+3≤K)
    (upper : t r (c+2)=9 ∨ t r (c+2)=73)
    (lower : t (r+1) (c+2)=9 ∨ t (r+1) (c+2)=73)
    (no192 : t r (c+1)≠192) (endM : t (r+1) (c+1)=128) :
    t (r+1) c=36 ∨ t (r+1) c=292 := by
  have P := (returnAt H acy score hk rl (by omega : 4≤c+1) rh (by omega)).1 upper lower
  have W := (returnAt H acy score hk rl cl rh (by omega)).2
  rcases P.2 endM with M|M|M
  · exact (W.1 M endM).2
  · exact .inr (W.2.1 M endM)
  · exact (no192 M).elim

/-- The predecessor strip either crosses the chosen incoming cut
or starts strictly below it with a classified source one row above. -/
theorem trace {s r c : Nat} (start : 4 ≤ s) (le : s≤r) (cl : 4≤c) (rh : r+2≤K) (ch : c+3≤K)
    (two : t r (c+1)=2) (down : t (r+1) (c+1)=258) (east : t r (c+2)=73) :
    ∃ b, s≤b ∧ b≤r ∧ (∀ i, b ≤ i → i≤r → Run (t i c) (t i (c+1)) (t i (c+2))) ∧
      (b=s ∨ s<b ∧ Source (t (b-1) c) (t (b-1) (c+1)) (t (b-1) (c+2))) := by
  have seed := (wordAt H acy score hk (by omega : 4≤r) cl rh (by omega)).1 two down
  have go (z : Nat) (lo : s≤z) (hi : z≤r) (old : Run (t z c) (t z (c+1)) (t z (c+2))) :
      ∃ b, s≤b ∧ b≤z ∧ (∀ i, b ≤ i → i≤z → Run (t i c) (t i (c+1)) (t i (c+2))) ∧
        (b=s ∨ s<b ∧ Source (t (b-1) c) (t (b-1) (c+1)) (t (b-1) (c+2))) := by
    induction z,lo using Nat.le_induction with
    | base => exact ⟨s,le_rfl,le_rfl,fun i l h => (show i=s by omega) ▸ old,.inl rfl⟩
    | succ z lo ih =>
      have L := wordAt H acy score hk (by omega : 4≤z) cl (by omega) (by omega)
      have R := wordAt H acy score hk (by omega : 4≤z) (by omega : 4≤c+1) (by omega) (by omega)
      rcases backward L R old with prev|birth
      · obtain ⟨b,bl,bh,strip,why⟩ := ih (by omega) prev
        refine ⟨b,bl,by omega,?_,why⟩
        intro i l h; by_cases h' : i≤z
        · exact strip i l h'
        · exact (show i=z+1 by omega) ▸ old
      · exact ⟨z+1,by omega,le_rfl,fun i l h => (show i=z+1 by omega) ▸ old,.inr ⟨by omega,birth⟩⟩
  exact go r le le_rfl ⟨seed,two,.inr east⟩

omit H acy score hk in
private theorem seal_no_center {x y : Nat} (yl : 5≤y) (xl : 6≤x) (yh : y+2≤K) (xh : x<K)
    (sealed' : Seal F v q x y) (age : (q:Int)-x+3≤3*(y:Int)-1) :
    bit (t (y-1) (x-1)) 4 ≠ 1 := by
  intro hit
  let r := 1+3*(y-1)+1
  let c := 1+3*(x-1)+1
  have mark : onSite F v r c=true := readBit 4 hit
  let p : Pos := ((r:Nat),(c:Nat))
  have inside : Camera.In (35+42*u) p := by dsimp [Camera.In,p,r,c]; omega
  let z := Camera.point u v p
  have loc : coordinates v z=p := Camera.coords_point inside
  have mem : z∈F := by
    change marked F (L7.view v (35+42*u:Nat) p.1 p.2)=true at mark
    rw [←Camera.coord_point inside,marked_at] at mark; exact of_decide_eq_true mark
  have eq := sealed'.1 z mem (by rw [loc]; dsimp [p,r]; omega) (by
    rw [loc]; refine ⟨(r:Int),?_,?_,?_⟩ <;> dsimp [p,r,c] <;> (try simp only [abs_eq_max_neg]) <;> omega)
  have h := eq.1
  rw [loc] at h; dsimp [p,c] at h; omega

/-- At a dangling leading edge the upper 16 need not have been
inside the initial plateau. If it is already there at the cut, the
physical seal rules out *both* of its non-73 predecessors. -/
theorem sealed_entry {x y : Nat} (yl : 5≤y) (xl : 6≤x) (yh : y+2≤K) (xh : x<K)
    (sealed' : Seal F v q x y) (age : (q:Int)-x+3≤3*(y:Int)-1)
    (left : t y (x-1)=16) (here : t y x=73) :
    t (y-1) (x-2)=2 ∧ t y (x-2)=258 ∧ t (y-1) (x-1)=73 := by
  have Z := seal_no_center yl xl yh xh sealed' age
  have L := (wordAt H acy score hk (by omega : 4≤y-1) (by omega : 4≤x-1) (by omega) (by omega)).2.2.2.2.2.1
  have R := (wordAt H acy score hk (by omega : 4≤y-1) (by omega : 4≤x-2) (by omega) (by omega)).2.2.2.2.2.2.1
  rw [show x-1+1=x by omega,show y-1+1=y by omega] at L
  rw [show x-2+1=x-1 by omega,show y-1+1=y by omega] at R
  have a : t (y-1) (x-1)=73 := by
    rcases L left here with a|a|a
    · exact (Z (by rw [a]; decide)).elim
    · exact (Z (by rw [a]; decide)).elim
    · exact a
  exact ⟨(R a left).1,(R a left).2,a⟩

def LiveSource (l m r : Nat) :=
  ((l=128 ∨ l=192) ∧ (m=8 ∨ m=9) ∧ (r=72 ∨ r=73)) ∨
  (l=292 ∧ m=36 ∧ r=128)

omit H acy score hk in
private theorem narrow {l m r : Nat} (S : Source l m r) (N : r≠144 ∧ r≠146 ∧ r≠384)
    (back : r=128 → m=36 ∨ m=292) (left : m=36 → l=292) :
    LiveSource l m r := by unfold Source at S; unfold LiveSource; grind

/-- The same physical ancestry for an interior or a leading-edge
read. A stationary run crossing the retained cut is impossible. -/
def History {u} (F : Finset (Site u)) (v : View) (x R : Nat) (read : Nat → Prop := fun _ => True) : Prop :=
  let mask := Rooted.tile F v
  ∃ s b h, 4 ≤ s ∧ s<b ∧ b≤h ∧ h<R ∧
    LiveSource (mask (b-1) (x-3)) (mask (b-1) (x-2)) (mask (b-1) (x-1)) ∧
    (∀ d, b ≤ d → d≤h → Run (mask d (x-3)) (mask d (x-2)) (mask d (x-1))) ∧
    mask h (x-2)=2 ∧ mask (h+1) (x-2)=258 ∧ mask h (x-1)=73 ∧
    (∀ d, h < d → d≤R → mask d (x-1)=16 ∧ mask d x=73) ∧ read (b-1)

set_option maxHeartbeats 700000 in
theorem from_prior {y f x j : Nat} (past : PriorCut F v y f) (left : f≤x) (xh : x<K)
    (rh : y+j+2≤K) (history : ∀ d≤j, t (y+d) x=73 ∨ t (y+d) x=9)
    (west : t (y+j) (x-1)=16) (here : t (y+j) x=73) : History F v x (y+j) := by
  obtain ⟨fl,s,sl,sy,plain,guards⟩ := past
  obtain ⟨clean,init⟩ := guards x left xh
  let D := y+j-s
  have time : s+D=y+j := by dsimp [D]; omega
  have hist (z : Nat) (lo : s≤z) (hi : z≤y+j) : t z x=73 ∨ t z x=9 := by
    by_cases early : z≤y
    · exact .inl (plain z lo early x left xh)
    · simpa only [show y+(z-y)=z by omega] using history (z-y) (by omega)
  obtain ⟨a,aj,m,n,p,strip⟩ := CornerCone.birth H acy score hk (y:=s) (j:=D) sl (by omega) (by omega)
    xh init (fun d hd => hist _ (by omega) (by omega)) (time ▸ west) (time ▸ here)
  let h := s+a
  let c := x-3
  have c1 : c+1=x-2 := by dsimp [c]; omega
  have c2 : c+2=x-1 := by dsimp [c]; omega
  obtain ⟨b,bl,bh,run,origin⟩ := trace H acy score hk (s:=s) (r:=h) (c:=c) sl (by dsimp [h]; omega)
    (by dsimp [c]; omega) (by dsimp [h]; omega) (by dsimp [c]; omega)
    (c1 ▸ m) (c1 ▸ n) (c2 ▸ p)
  rw [c1,c2] at run origin
  rcases origin with rfl|⟨sb,src⟩
  · exact (clean (run _ le_rfl bh).2.1).elim
  have tip := hist (b-1) (by omega) (by dsimp [h] at bh; omega)
  have T := (wordAt H acy score hk (by omega : 4≤b-1) (by omega : 4≤x-1)
    (by dsimp [h] at bh; omega) (by omega)).2.2.2.2.2.2.2
  rw [show x-1+1=x by omega] at T
  have never (z : Nat) (lo : s≤z) (hi : z≤y+j) : t z (x-1)≠192 := by
    induction z,lo using Nat.le_induction with
    | base =>
      change t s (x-1)=73 at init
      omega
    | succ z lo ih =>
      have P := (returnAt H acy score hk (by omega : 4≤z) (by omega : 4≤x-1) (by omega) (by omega)).1
      rw [show x-1+1=x by omega] at P
      exact fun M => ih (by omega) ((P (hist z lo (by omega)).symm (hist _ (by omega) hi).symm).1 M)
  have back (endM : t (b-1) (x-1)=128) : t (b-1) (x-2)=36 ∨ t (b-1) (x-2)=292 := by
    have earlier : s<b-1 := by
      by_contra! e
      rw [show b-1=s by omega] at endM
      change t s (x-1)=73 at init
      omega
    have P := before128 H acy score hk (by omega : 4≤b-2) (by omega : 4≤x-2)
      (by dsimp [h] at bh; omega) (by omega)
    simp only [show x-2+1=x-1 by omega,show x-2+2=x by omega,show b-2+1=b-1 by omega] at P
    exact P (hist _ (by omega) (by dsimp [h] at bh; omega)).symm tip.symm
      (never _ (by omega) (by dsimp [h] at bh; omega)) endM
  have left36 := (returnAt H acy score hk (by omega : 4≤b-1) (by dsimp [c]; omega : 4≤c)
    (by dsimp [h] at bh; omega) (by dsimp [c]; omega)).2.2.2
  rw [c1,show b-1+1=b by omega] at left36
  refine ⟨s,b,h,sl,sb,bh,by dsimp [h]; omega,
    narrow src (T tip.symm) back (fun M => left36 M (run b le_rfl bh).2.1),run,m,n,p,?_,trivial⟩
  intro d hd dh
  simpa only [show s+(d-s)=d by dsimp [h] at hd; omega] using
    strip (d-s) (by dsimp [h] at hd; omega) (by omega)
end
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.TwoAncestry
