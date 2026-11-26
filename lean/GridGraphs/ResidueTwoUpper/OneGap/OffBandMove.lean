import GridGraphs.ResidueTwoUpper.OneGap.FanSpeedTail
import GridGraphs.ResidueTwoUpper.OneGap.CornerDrift
import GridGraphs.ResidueTwoUpper.OneGap.TwoAncestry
import GridGraphs.ResidueTwoUpper.OneGap.DepartureRim

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero FanSlab BoundarySix.Connected SouthCap
open L7 hiding band
open SouthCap.Strip.GridScan.Rooted.Buffered
local notation "TILE" => SouthCap.Strip.GridScan.Rooted.tile

open SouthCap.Strip.GridScan.Rooted SouthCap.Strip.GridScan
open SouthCap.Strip hiding band

/-- The only ways the leading vertical edge can leave the band below a rigid row. -/
def breakPair (a b : Nat) := [(9,2),(9,146),(73,16),(73,129),(73,144)].contains (a,b)
private theorem narrow {a b : Nat} (h : breakPair a b=true) (m : b≠144) (n : b≠146) :
    [(9,2),(73,16),(73,129)].contains (a,b)=true := by
  simp [breakPair,m,n] at h
  simpa using h
private theorem upper129 {a b : Nat} (h : [(9,2),(73,16),(73,129)].contains (a,b)=true) (e : b=129) :
    a=73 := by subst b; simpa using h
private def firstLaw (w : Word) : Prop :=
  let (a,b,c,d) := w
  (a=9 ∨ a=73) → b=73 → (edge₃ a c=true ∨ breakPair a c=true) ∧
    (c=146 → d=144) ∧ (c=144 → d=129)
private instance (w : Word) : Decidable (firstLaw w) := by unfold firstLaw; infer_instance
private theorem firstCheck : ∀ s e : Fin 7, (bankWords (6+s.val) (6+e.val)).all
    (fun w => decide (firstLaw w))=true := by native_decide

def FirstBreak {u} (F : Finset (Site u)) (w : View) (y x j : Nat) : Prop :=
  ([(9,2),(73,16),(73,129)].contains (TILE F w (y+j) x,TILE F w (y+j+1) x)) ∧
  (TILE F w (y+j+1) x=129 → 5≤x →
    TILE F w (y+j+1) (x+1)=73 ∧ TILE F w (y+j+2) x=128 ∧
    TILE F w (y+j) (x-1)=16 ∧ TILE F w (y+j+1) (x-1)=16 ∧ TILE F w (y+j+2) (x-1)=292) ∧
  ∀ d ≤ j, ∀ i, x ≤ i → i<11+14*u →
    TILE F w (y+d) i=73 ∨ i=x ∧ TILE F w (y+d) i=9

set_option maxHeartbeats 1500000 in
theorem first_break_of_block {u F w q} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y f x W h : Nat} (front : Front F w q (11+14*u) y f)
    (yl : 4≤y) (fl : 4≤f) (left : f≤x) (width : x+W+2≤11+14*u)
    (margin : x+5≤11+14*u) (height : y+h+2≤11+14*u) (feet : q+2≤11+14*u) (bad : ¬Straight F w y x W h) :
    ∃ j<h, FirstBreak F w y x j := by
  let k := 11+14*u
  let t := TILE F w
  let reg := fun d => ∀ i, x ≤ i → i<k → t (y+d) i=73 ∨ i=x ∧ t (y+d) i=9
  by_contra! free
  have states (j : Nat) (jh : j≤h) : RootLine F w (k-1) (y+j) ∧ ∀ d≤j, reg d := by
    induction j with
    | zero =>
      refine ⟨front.2.2 _ (by dsimp [k]; omega) (by dsimp [k]; omega) (by dsimp [k]; omega),?_⟩
      intro d hd i il ih
      obtain rfl : d=0 := by omega
      exact .inl (front.1 y le_rfl le_rfl i (by omega) ih)
    | succ j ih =>
      obtain ⟨line,prior⟩ := ih (by omega)
      have upper := prior j le_rfl
      have body (i : Nat) (lo : x < i) (hi : i<k) : t (y+j) i=73 := by
        rcases upper i (by omega) hi with m|⟨e,_⟩ <;> solve | exact m | omega
      have rh : y+j+2≤k := by dsimp [k]; omega
      have ch : x+2≤k := by dsimp [k]; omega
      have mem := board_word H acy score hk (by omega : 4≤y+j) (by omega : 4≤x) rh ch
      have R := tag_range rh; have C := tag_range ch
      have test := firstCheck ⟨endTag k (y+j)-6,by omega⟩ ⟨endTag k x-6,by omega⟩
      dsimp only at test
      rw [show 6+(endTag k (y+j)-6)=endTag k (y+j) by omega,
        show 6+(endTag k x-6)=endTag k x by omega] at test
      have head := upper x le_rfl (by omega)
      have law : firstLaw (SouthCap.Strip.word t (y+j) x) := of_decide_eq_true (List.all_eq_true.mp test _ mem)
      have edge := law (head.elim Or.inr (fun p => .inl p.2)) (body _ (by omega) (by omega))
      rcases edge.1 with stable|br
      · have row : BandRow t (y+j) x k := by
          intro i l h'
          rw [body (i+1) (by omega) (by omega)]
          rcases upper i l (by omega) with m|⟨_,m⟩ <;> rw [m] <;> decide
        have lower := (across H acy score hk (by omega) (by omega) rh row stable).1
        have last := body (k-1) (by omega) (by omega)
        dsimp only [t] at last
        have next := extend_line (y:=y+j) line (by rw [last]; decide) (.inl (by rw [last]; decide))
        have reg' := rigid H acy one score hk (by omega) (by dsimp [k] at *; omega)
          (by omega) ch lower next
        refine ⟨next,fun d hd => ?_⟩
        rcases Nat.lt_or_eq_of_le hd with lt|rfl
        · exact prior d (by omega)
        · exact reg'
      · have follow (i : Nat) (il : x < i) (room : i+4≤k) (hit : t (y+j+1) i=144) : False := by
          have M := board_word H acy score hk (by omega : 4≤y+j) (by omega : 4 ≤ i) rh (by dsimp [k] at *; omega)
          have C' := tag_range (show i+2≤k by omega)
          have test' := firstCheck ⟨endTag k (y+j)-6,by omega⟩ ⟨endTag k i-6,by omega⟩
          dsimp only at test'
          rw [show 6+(endTag k (y+j)-6)=endTag k (y+j) by omega,
            show 6+(endTag k i-6)=endTag k i by omega] at test'
          have law' : firstLaw (Strip.word t (y+j) i) := of_decide_eq_true (List.all_eq_true.mp test' _ M)
          have tip := (law' (.inr (body i il (by omega))) (body _ (by omega) (by omega))).2.2 hit
          have forced := Break129.forced_corner H acy one score hk (by omega) (by omega)
            (by omega) (by dsimp [k] at *; omega) (fun c l h => body c (by omega) h) tip line
          have eq := forced.2.2.2.1
          simp only [Nat.add_sub_cancel] at eq
          exact (by change t (y+j+1) i=16 at eq; omega)
        have corner {i : Nat} (l : x < i) (room : i+3≤k) (m : t (y+j+1) i=129) :=
          Break129.forced_corner H acy one score hk (by omega) (by omega : 5 ≤ i) (by omega)
            room (fun c lo h => body c (by omega) h) m line
        have n144 (hit : t (y+j+1) x=144) : False := by
          have eq := (corner (by omega : x<x+1) (by dsimp [k]; omega) (edge.2.2 hit)).2.2.2.1
          change t (y+j+1) x=16 at eq
          omega
        have n146 (hit : t (y+j+1) x=146) : False :=
          follow (x+1) (by omega) (by dsimp [k]; omega) (edge.2.1 hit)
        have small := narrow br n144 n146
        apply False.elim (free j (by omega) ⟨small,?_,prior⟩)
        intro hit cl
        have A := upper129 (a:=t (y+j) x) (b:=t (y+j+1) x) small hit
        apply Break129.forced_corner H acy one score hk (by omega) cl (by omega) (by omega) _ hit line
        intro c lo h
        rcases Nat.eq_or_lt_of_le lo with rfl|lt
        · exact A
        · exact body _ lt h
  apply bad
  intro j jh i ih
  rcases (states j jh).2 j le_rfl (x+i) (by omega) (by dsimp [k]; omega) with m|⟨_,m⟩ <;>
    change t (y+j) (x+i)∈Port.shapes <;> rw [m] <;> decide

set_option maxHeartbeats 700000 in
/-- A blocked window cannot be explained by a 3 or 7 inside an otherwise
admitted band. The backward search need only go as far east as the
three-columns-per-row boundary, regardless of the side length. -/
theorem off_band_of_block {u F w q} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y f x W h : Nat} (front : Front F w q (11+14*u) y f)
    (yl : 4≤y) (fl : 4≤f) (left : f≤x) (width : x+W+2≤11+14*u)
    (height : y+h+2≤11+14*u) (feet : q+2≤11+14*u) (bad : ¬Straight F w y x W h) :
    ∃ j, 1≤j ∧ j≤h ∧ ∃ c, x ≤ c ∧ c<11+14*u ∧ c≤f+3*j ∧
      bandMask (TILE F w (y+j) c)=false := by
  let k := 11+14*u
  by_contra! allGood
  have bands := bands_below H acy one score hk (D:=h) yl fl (by omega)
    (front.1 y le_rfl le_rfl)
  have masks (j i : Nat) (jl : 1≤j) (jh : j≤h) (il : x ≤ i) (ih : i<k) :
      bandMask (TILE F w (y+j) i) := by
    by_cases near : i≤f+3*j
    · simpa using allGood j jl jh i il ih near
    · by_cases last : i=k-1
      · have p := bands j jh (i-1) (by omega) (by omega)
        rw [show i-1+1=i by omega] at p
        have tail {a b : Nat} (p : band a b=true) : bandMask b=true := by
          simp [band] at p
          rcases p with h|h|h|h|h|h|h <;> rw [h.2] <;> decide
        exact tail p
      · exact band_left_mask (bands j jh i (by omega) (by dsimp [k] at *; omega))
  have states (j : Nat) (jh : j≤h) :
      RootLine F w (k-1) (y+j) ∧ ∀ i, x ≤ i → i<k →
        TILE F w (y+j) i=73 ∨ i=x ∧ TILE F w (y+j) i=9 := by
    induction j with
    | zero => exact ⟨front.2.2 _ (by dsimp [k]; omega) (by omega) (by dsimp [k]; omega),
        fun i l h => .inl (front.1 _ le_rfl le_rfl _ (by omega) h)⟩
    | succ j ih =>
      obtain ⟨line,upper⟩ := ih (by omega)
      have last : TILE F w (y+j) (k-1)=73 := by
        rcases upper (k-1) (by dsimp [k]; omega) (by omega) with m|⟨e,_⟩
        · exact m
        · dsimp [k] at e; omega
      have next := SouthCap.Strip.GridScan.Rooted.extend_line (y:=y+j) line
        (by rw [last]; decide) (.inl (by rw [last]; decide))
      have row : BandRow (TILE F w) (y+(j+1)) x k := by
        intro i l h'
        exact physical_pair (r:=y+(j+1)) (c:=i) H acy score hk (by omega) (by omega)
          (by omega) h' (masks (j+1) i (by omega) jh l (by omega))
          (masks (j+1) (i+1) (by omega) jh (by omega) (by omega))
      exact ⟨next,rigid (y:=y+(j+1)) (a:=x) H acy one score hk (by omega) (by omega)
        (by omega) (by omega) row next⟩
  apply bad
  intro j jh i ih
  rcases (states j jh).2 (x+i) (by omega) (by dsimp [k]; omega) with m|⟨_,m⟩ <;>
    change TILE F w (y+j) (x+i)∈Port.shapes <;> rw [m] <;> decide

def CornerHistory {u} (F : Finset (Site u)) (w : View) (y f x j : Nat) : Prop :=
  TILE F w (y+j+1) x=129 → 5≤x →
    x ≤ max 5 f+3*(j/4)+j%4 ∧ (∀ i, 4 ≤ i → i+1 < x →
      (TILE F w (y+j) i=258 ∨ TILE F w (y+j) i=288 ∨ TILE F w (y+j) i=292) ∧
      TILE F w (y+j+1) i=292 ∧ TILE F w (y+j+2) i=292) ∧
    (f < x → 6≤x → ∃ h<j, TILE F w (y+h) (x-2)=2 ∧ TILE F w (y+h+1) (x-2)=258 ∧
      TILE F w (y+h) (x-1)=73 ∧ ∀ d, h < d → d≤j →
        TILE F w (y+d) (x-1)=16 ∧ TILE F w (y+d) x=73)

theorem west_of_first_break {u F w q} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    {y f x j : Nat} (front : Front F w q (11+14*u) y f)
    (yl : 4≤y) (height : y+j+3≤11+14*u) (width : x+4≤11+14*u) (left : f≤x)
    (feet : q+2≤11+14*u) (br : FirstBreak F w y x j) : CornerHistory F w y f x j := by
  intro hit xl
  obtain ⟨_,_,A,B,C⟩ := br.2.1 hit xl
  refine ⟨?_,(fun i l h => CornerCone.west_trace H acy score hk (by omega) height (by omega)
    A B C i l (by omega)),?_⟩
  swap
  · intro inside room
    exact CornerCone.birth H acy score hk yl room (by omega) (by omega)
      (front.1 y le_rfl le_rfl _ (by omega) (by omega))
      (fun d hd => (br.2.2 d hd x le_rfl (by omega)).imp_right And.right)
      A (upper129 br.1 hit)
  by_contra! overlap
  let k := 11+14*u
  have mid := CornerCone.blocks H acy one score hk (a:=max 5 f) (y:=y) (s:=j/4)
    (f:=k-1) yl (by omega) (by omega) (by omega) (by dsimp [k]; omega) (by dsimp [k]; omega)
    (fun i l h => front.1 y le_rfl le_rfl i (by omega) h)
    (fun i l h => front.2.2 i (by dsimp [k] at l; omega) h (by dsimp [k] at l; omega))
  have old := CornerCone.cone H acy one score hk (D:=j%4)
    (by omega) (by omega) (by omega) (by omega) (by dsimp [k]; omega) mid.1 mid.2 (by dsimp [k]; omega)
    (j%4) le_rfl
  have bad := old.1 (x-1) (by omega) (by omega)
  rw [show y+4*(j/4)+j%4=y+j by omega] at bad
  omega

/-- The first departure from the actual straight-mask window and the
129 ancestry, when present, use one parent field on the scored square. -/
def Observed {u} (F : Finset (Site u)) (v : View) (y x W h d : Nat) :=
  ∃ j i, Departure.First F v y x W h j i ∧ ∃ Q : Flow F,
    (TILE F v (y+j) (x+i),Departure.center Q v (y+j) (x+i))∈
      Departure.exits (decide (i=0)) (Departure.headDir Q v (y+j) (x+i)==3) ∧
    (0 < i → ¬RootLine F v (x+i) (y+j)) ∧
    (TILE F v (y+d+1) x=129 → d+3<j ∧
      TwoAncestry.History F v x (y+d) (fun r => Departure.SourceEdges Q v r (x-2)))

theorem observed_of_break {u F w q y x f d W h} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u)
    (front : Front F w q (11+14*u) y f) (left : f≤x) (yl : 4≤y) (xl : 7≤x) (ww : 1≤W)
    (ht : y+h+8≤11+14*u) (wc : x+W+8≤11+14*u) (feet : q+2≤11+14*u)
    (dh : d<h) (br : FirstBreak F w y x d) (past : PriorCut F w y f) (bad : ¬Straight F w y x W h) :
    Observed F w y x W h d := by
  obtain ⟨j,i,bad'⟩ := Departure.first_of_bad front left (by omega) bad
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  have prices := prices_of_seed u q F acy w H.parent H.step H.patches H.stars
  have out := Departure.forced_exit_at H acy score hk Q prices yl xl ww ht wc bad'
  refine ⟨j,i,bad',Q,out,?_,?_⟩
  · intro pos
    have h' := bad'.2.1; have w' := bad'.2.2.1
    apply Departure.no_inner_north Q (by omega) (by omega)
    simpa only [show decide (i=0)=false by simp [Nat.ne_of_gt pos]] using out
  intro hit
  have prior := br.2.2
  have src := TwoAncestry.from_prior H acy score hk past left (by omega) (by omega)
    (fun z hz => (prior z hz _ le_rfl (by omega)).imp_right And.right)
    (br.2.1 hit (by omega)).2.2.1 (upper129 br.1 hit)
  refine ⟨?_,Departure.owned_history Q prices xl (by omega) (by omega) src⟩
  let k := 11+14*u
  have endLine (z : Nat) (hz : z≤d) : RootLine F w (k-1) (y+z) := by
    induction z with
    | zero => exact front.2.2 _ (by dsimp [k]; omega) (by dsimp [k]; omega) (by dsimp [k]; omega)
    | succ z ih =>
      have m : TILE F w (y+z) (k-1)=73 := by
        rcases prior z (by omega) (k-1) (by dsimp [k]; omega) (by dsimp [k]; omega) with m|⟨eq,_⟩
        · exact m
        · dsimp [k] at eq; omega
      exact extend_line (y:=y+z) (ih (by omega)) (by rw [m]; decide) (.inl (by rw [m]; decide))
  have top (c : Nat) (l : x ≤ c) (h : c<k) : TILE F w (y+d) c=73 := by
    rcases prior d le_rfl c l h with m|⟨rfl,_⟩
    · exact m
    · exact upper129 br.1 hit
  have hold := Departure.three_after H acy one score hk (by omega) (by omega) (by omega) (by omega)
    top (endLine d le_rfl) hit
  have iw := bad'.2.2.1
  by_contra! early
  apply bad'.2.2.2.1
  by_cases pre : j≤d
  · rcases prior j pre (x+i) (by omega) (by omega) with m|⟨_,m⟩ <;> rw [m] <;> decide
  · simpa only [show y+d+(j-d)=y+j by omega] using
      hold (j-d) (by omega) (by omega) (x+i) (by omega) (by omega)

def OffBandMove {u} (F : Finset (Site u)) (w : View) (q y0 : Nat) : Prop :=
  let k := 11+14*u
  ∃ (p : Speed.State) (m : Speed.Move), m∈Speed.moves ∧ Speed.fits k q m p ∧
    Speed.Reaches k q (Speed.next m q p) ∧ p.1≤k ∧ y0≤k-p.1 ∧ 4≤p.2 ∧
    Front F w q k (k-p.1) p.2 ∧ ¬Straight F w (k-p.1) (Speed.x m q p.2) (m.width-1) (m.height-1) ∧
    (∃ j : Nat, 1≤j ∧ j < m.height ∧ ∃ c, Speed.x m q p.2 ≤ c ∧ c<k ∧ c≤p.2+3*j ∧
      bandMask (TILE F w (k-p.1+j) c)=false) ∧
    ∃ j < m.height-1, FirstBreak F w (k-p.1) (Speed.x m q p.2) j ∧
      CornerHistory F w (k-p.1) p.2 (Speed.x m q p.2) j ∧
      (TILE F w (k-p.1+j+1) (Speed.x m q p.2)=129 →
        TwoAncestry.History F w (Speed.x m q p.2) (k-p.1+j)) ∧
      Observed F w (k-p.1) (Speed.x m q p.2) (m.width-1) (m.height-1) j ∧ ¬Speed.widthRoom k m p

theorem off_band_of_score {u F w q y0} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 53≤11+14*u) (lo : 4≤y0)
    (feet : q+2≤11+14*u) (bad : BlockedMove F w q y0) : OffBandMove F w q y0 := by
  obtain ⟨p,m,mem,fit,path,lim,birth,fl,front,blocked,past⟩ := bad
  have left : p.2≤Speed.x m q p.2 := by unfold Speed.x; split <;> omega
  have wide := fit.1
  have hi := fit.2.2
  obtain ⟨j,jl,jh,c,tail⟩ := off_band_of_block H acy one score hk front
    (by omega) fl left (by omega) (by omega) feet blocked
  obtain ⟨d,dh,br⟩ := first_break_of_block H acy one score hk front (by omega) fl left
    (by omega) (by omega) (by omega) feet blocked
  refine ⟨p,m,mem,fit,path,lim,birth,fl,front,blocked,⟨j,jl,by omega,c,tail⟩,d,dh,br,
    west_of_first_break H acy one score hk front (by omega) (by omega) (by omega) left feet br,?_,?_,?_⟩
  rotate_left 2
  · intro room
    have wpos : 2 ≤ m.width ∧ 1 ≤ m.height := by
      simp [Speed.moves] at mem; rcases mem with rfl|rfl|rfl|rfl|rfl <;> decide
    obtain ⟨Q⟩ := flow_of_score u F acy score one
    exact blocked (Departure.straight_of_room H acy one score hk Q
      (prices_of_seed u q F acy w H.parent H.step H.patches H.stars) front left (by omega) past.1
      (by omega) (by omega) room feet)
  swap
  · have wpos : 2 ≤ m.width ∧ 1 ≤ m.height := by
      simp [Speed.moves] at mem; rcases mem with rfl|rfl|rfl|rfl|rfl <;> decide
    have fl' := past.1
    apply observed_of_break H acy one score hk front left (by omega) (by omega) (by omega)
      (by omega) (by omega) feet dh br past blocked
  intro hit
  have room := past.1
  exact TwoAncestry.from_prior H acy score hk past left (by omega) (by omega)
    (fun z hz => (br.2.2 z hz _ le_rfl (by omega)).imp_right And.right)
    (br.2.1 hit (by omega)).2.2.1 (upper129 br.1 hit)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
