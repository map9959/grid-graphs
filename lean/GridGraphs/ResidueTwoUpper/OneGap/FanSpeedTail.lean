import GridGraphs.ResidueTwoUpper.OneGap.FanRootSpeed
import GridGraphs.ResidueTwoUpper.OneGap.FanLastLine
import GridGraphs.ResidueTwoUpper.OneGap.FanLongSchedules
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSeed FanSlab Camera Port ResidueZero Stencil BoundarySix.Connected

/-- The thirteen-mask hypothesis is needed only where the moving
window actually reads tiles. Rim rectangles are not assigned bulk tags. -/
def DeepAfter {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (y0 : Nat) :=
  ∀ j i : Nat, y0≤j → j+7≤11+14*u → 4≤ i → i+7≤11+14*u → square F w (1+3*j) (1+3*i)∈shapes

def SouthEnd {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (q : Nat) :=
  ∃ h f, Speed.cap (11+14*u) (h,f) ∧ Front F w q (11+14*u) (11+14*u-h) f

/-- A real earlier cut protects two columns even for a leading-edge read. -/
def PriorCut {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (y f : Nat) :=
  7≤f ∧ ∃ b, 4≤b ∧ b≤y ∧ Plateau F w b y f (11+14*u) ∧
    ∀ i, f ≤ i → i<11+14*u →
      square F w (1+3*b) (1+3*(i-2))≠2 ∧ square F w (1+3*b) (1+3*(i-1))=73

/-- A candidate counterexample to a speed move must have a physical
incoming front and must itself be on a move with a route to the cap. -/
def BlockedMove {u} (F : Finset (GridVertex (N u) (N u))) (w : View) (q y0 : Nat) : Prop :=
  let k := 11+14*u
  ∃ (p : Speed.State) (m : Speed.Move), m∈Speed.moves ∧ Speed.fits k q m p ∧
    Speed.Reaches k q (Speed.next m q p) ∧ p.1≤k ∧ y0≤k-p.1 ∧ 4≤p.2 ∧
    Front F w q k (k-p.1) p.2 ∧
    ¬Straight F w (k-p.1) (Speed.x m q p.2) (m.width-1) (m.height-1) ∧ PriorCut F w (k-p.1) p.2

theorem advance_fitted {u q} {F : Finset (GridVertex (N u) (N u))} (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) {p : Speed.State} {m : Speed.Move} (mem : m∈Speed.moves) (fit : Speed.fits (11+14*u) q m p)
    (lim : p.1≤11+14*u) (hf : 4≤p.2) :
    let k := 11+14*u; let y := k-p.1; let x := Speed.x m q p.2
    4≤y → (q:Int)-p.2+3≤3*(y:Int) → Front F w q k y p.2 →
    Straight F w y x (m.width-1) (m.height-1) →
      Front F w q k (y+m.s) (x+m.d) ∧ Plateau F w y (y+m.s) (x+m.d) k := by
  intro k y x hy birth fr deep'
  have md : 1 ≤ m.d := by simp [Speed.moves] at mem; rcases mem with rfl|rfl|rfl|rfl|rfl <;> decide
  obtain ⟨ww,dt,hh⟩ := fit
  have fx : p.2≤x := by unfold x Speed.x; split <;> omega
  have roomX : x+m.width+7≤ k := ww
  have roomY : y+m.height+7≤ k := by dsimp [y,k]; omega
  by_cases isRoot : m.rooted=true
  · have E : m=Speed.root := by simp [Speed.moves] at mem; rcases mem with h|h|h|h|h <;> subst m <;> first | rfl | contradiction
    subst m
    apply physical_root_step_rect u q y p.2 x (by dsimp [x,Speed.x,Speed.root]; omega) fx _ F acy w P step clean zero Q deep' fr
    change x+10+7≤ k at roomX; change y+10+7≤ k at roomY; dsimp [k] at *; omega
  · have b : m.rooted=false := Bool.eq_false_iff.mpr isRoot
    have edge := dt b; change x+m.width≤q+1 at edge
    have xp : x=p.2 := by simp [x,Speed.x,b]
    have test' : ∃ rounds, test (m.width-1) (m.height-1) (m.d-1) m.s rounds true := by
      simp [Speed.moves] at mem; rcases mem with h|h|h|h|h <;> subst m
      · exact ⟨9,long_test⟩
      · exact ⟨7,medium_test⟩
      · exact ⟨6,short_test⟩
      · exact ⟨4,tiny_test⟩
      · contradiction
    have win : m.s< m.height-1 ∧ m.d-1< m.width-1 := by simp [Speed.moves] at mem; rcases mem with h|h|h|h|h <;> subst m <;> decide
    obtain ⟨n,ck⟩ := test'
    have z := physical_dangling_step_rect u q y x _ _ _ _ _ ck win (by dsimp [k] at *; omega) (by omega)
      (by push_cast at *; omega) F acy w P step clean zero Q deep' (xp ▸ fr)
    refine ⟨by simpa only [show x+(m.d-1)+1=x+m.d by omega] using z.1,?_⟩
    exact fun r lo hi i l h => z.2 r lo hi i (by omega) h

theorem follow_unblocked (u q : Nat) (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (y0 : Nat) (clear : ¬BlockedMove F w q y0) :
    ∀ p, Speed.Reaches (11+14*u) q p → let y := 11+14*u-p.1
      p.1≤11+14*u → y0≤y → 4≤y → 4≤p.2 → (q:Int)-p.2+3≤3*(y:Int) → Front F w q (11+14*u) y p.2 →
        (¬DeepAfter F w y0 → PriorCut F w y p.2) → SouthEnd F w q := by
  intro p sched; induction sched with
  | capEnd p h => dsimp only; intro _ _ _ _ _ fr _; exact ⟨p.1,p.2,h,fr⟩
  | via p m mem fit tail ih =>
    dsimp only at ih ⊢; intro hp hy0 hy hf birth fr past
    let k := 11+14*u; let y := k-p.1; let x := Speed.x m q p.2
    have props : m.s≤ m.height ∧ 1≤ m.width ∧ 1≤ m.height ∧ 1≤ m.d := by simp [Speed.moves] at mem; rcases mem with e|e|e|e|e <;> subst m <;> decide
    obtain ⟨ww,dt,hh⟩ := fit
    have fx : p.2≤x := by unfold x Speed.x; split <;> omega
    have roomX : x+m.width+7≤ k := ww
    have roomY : y+m.height+7≤ k := by dsimp [y,k]; omega
    have deep' : Straight F w y x (m.width-1) (m.height-1) := by
     by_contra bad
     apply clear ⟨p,m,mem,⟨ww,dt,hh⟩,tail,hp,hy0,hf,fr,bad,past ?_⟩
     intro deep; apply bad; intro j hj i hi
     apply deep <;> dsimp [k,y] at * <;> omega
    have newY : k-(Speed.next m q p).1=y+m.s := by dsimp [Speed.next,y,k]; omega
    suffices hand : Front F w q k (y+m.s) (x+m.d) ∧ Plateau F w y (y+m.s) (x+m.d) k by
      have md : 3 ≤ m.d := by simp [Speed.moves] at mem; rcases mem with e|e|e|e|e <;> subst m <;> decide
      apply ih (by dsimp [Speed.next]; omega) (by rw [newY]; omega) (by rw [newY]; omega) (by change 4≤ x+m.d; omega)
      · change (q:Int)-(x+m.d:Nat)+3≤3*((k-(Speed.next m q p).1:Nat):Int); rw [newY]; push_cast; omega
      · change Front F w q k (k-(Speed.next m q p).1) (x+m.d); rw [newY]; exact hand.1
      · intro _; change PriorCut F w (k-(Speed.next m q p).1) (x+m.d); rw [newY]
        refine ⟨by omega,y,hy,by omega,hand.2,?_⟩
        intro i l h
        have Z := fr.1 y le_rfl le_rfl (i-2) (by omega) (by omega)
        exact ⟨by rw [Z]; decide,fr.1 y le_rfl le_rfl (i-1) (by omega) (by omega)⟩
    exact advance_fitted acy w P step clean zero Q mem ⟨ww,dt,hh⟩ hp hf hy birth fr deep'

theorem no_blocked_of_deep {u w q y0} {F : Finset (GridVertex (N u) (N u))}
    (deep : DeepAfter F w y0) : ¬BlockedMove F w q y0 := by
  rintro ⟨p,m,mem,⟨ww,_,hh⟩,_,hp,hy,hf,_,bad,_⟩
  have pos : 1 ≤ m.width ∧ 1 ≤ m.height := by
    simp [Speed.moves] at mem; rcases mem with h|h|h|h|h <;> subst m <;> decide
  have fx : p.2≤Speed.x m q p.2 := by unfold Speed.x; split <;> omega
  apply bad
  intro j hj i hi
  apply deep <;> omega

theorem follow (u q : Nat) (_qfit : q+2≤11+14*u) (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (y0 : Nat) (deep : DeepAfter F w y0) :
    ∀ p, Speed.Reaches (11+14*u) q p → let y := 11+14*u-p.1
      p.1≤11+14*u → y0≤y → 4≤y → 4≤p.2 → (q:Int)-p.2+3≤3*(y:Int) → Front F w q (11+14*u) y p.2 → SouthEnd F w q :=
  fun p sched lim birth yl fl age fr => follow_unblocked u q F acy w P step clean zero Q y0
    (no_blocked_of_deep deep) p sched lim birth yl fl age fr (fun neg => (neg deep).elim)

/-- Expose the remaining-height catalogue as two explicit physical
predicates; the speed schedule itself has no local-window assumptions. -/
theorem to_south_end_unblocked (u q : Nat) (big : 57≤q) (qfit : q+2≤11+14*u) (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (sched : Speed.Reaches (11+14*u) q (Speed.start (11+14*u) q)) :
    let Y := (q-15)/6
    Front F w q (11+14*u) (Y+2) (q-3*Y+3) → Plateau F w (Y+2) (Y+6) (q-3*Y+2) (11+14*u) →
    (¬DeepAfter F w (Y+6) → PriorCut F w (Y+6) (q-3*Y+3)) → (¬BlockedMove F w q (Y+6)) → SouthEnd F w q := by
  intro Y fr rect past deep
  have room : 6*Y+15≤q ∧ q≤6*Y+20 := by dsimp [Y]; omega
  have next := advance_front F w (by omega) le_rfl (by omega) (fun t st rt => by push_cast at *; omega) fr rect
  have h := follow_unblocked u q F acy w P step clean zero Q (Y+6) deep _ sched
  dsimp only [Speed.start] at h
  apply h (by omega) (by dsimp [Y]; omega) (by omega) (by omega) (by push_cast; omega)
  · convert next using 2 <;> dsimp [Y] <;> omega
  · convert past using 2 <;> dsimp [Y] <;> omega

theorem to_south_end (u q : Nat) (big : 57≤q) (qfit : q+2≤11+14*u) (F : Finset (GridVertex (N u) (N u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (N u) (N u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p)) (clean : ∀ a,patchSlack F a=0)
    (zero : ∀ p,coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (Q : Flow F) (sched : Speed.Reaches (11+14*u) q (Speed.start (11+14*u) q)) :
    let Y := (q-15)/6
    Front F w q (11+14*u) (Y+2) (q-3*Y+3) → Plateau F w (Y+2) (Y+6) (q-3*Y+2) (11+14*u) → DeepAfter F w (Y+6) → SouthEnd F w q :=
  fun front plateau deep => to_south_end_unblocked u q big qfit F acy w P step clean zero Q sched
    front plateau (fun neg => (neg deep).elim) (no_blocked_of_deep deep)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
