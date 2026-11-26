import GridGraphs.ResidueTwoUpper.OneGap.FanTeethScan
import GridGraphs.ResidueTwoUpper.OneGap.FanElbow
import GridGraphs.ResidueTwoUpper.OneGap.FanBootGeo

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Teeth
open ResidueZero Stencil L7 FanSweep FanSlab FanSeed BoundarySix.Connected

def foldPre (b i c : Nat) := if b<4 ∨ c<6 then c else if c<9+3*(i-b) then 6+(c-6)%3 else c-3*(i-b)
def foldSide (u c : Nat) := if c<9 then c else if c<12+42*u then 9+(c-9)%3 else c-42*u

private theorem cmask (u c : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View) :
    lane (square F w 1 (1+c)) 4=(marked F (L7.view w (35+42*u:Nat) 2 (2+c:Nat))).toNat := by
  have h := (unpack (fun b : Fin 9 => marked F (L7.view w (35+42*u:Nat) (1+b.val/3:Nat) (1+c+b.val%3:Nat)))).2 4
  exact h.trans (by change (marked F (L7.view w _ 2 (1+c+1:Nat))).toNat=_; rw [show 1+c+1=2+c by omega])

private theorem path_of_marks {u last : Nat} (B : Box) (C : Nat → Nat)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View) (lo : C 0=0) (hi : C last=B.cols)
    (bd : ∀ c≤last, C c≤B.cols) (go : ∀ c<last, C (c+1)∈pred B false (C c) ∧ C c∈pred B true (C (c+1)))
    (ad : Nat → Nat → Nat → Bool) (empty : ∀ T : Path B, Kept T (build B fun r c => (List.range 512).filter (ad r c)) → False)
    (valid : ∀ r≤B.rows, ∀ c≤last, ad r (C c) (square F w (1+r) (1+c))) : False := by
  let T : Path B := {
    last:=last, col:=C, M:=fun r c => square F w (1+r) (1+c), start:=lo, stop:=hi, bound:=bd, next:=go
    across:=fun r _ c _ => by simpa [Nat.add_assoc] using square_meet F w (1+r) (1+c) false
    down:=fun r _ c _ => by simpa [Nat.add_assoc] using square_meet F w (1+r) (1+c) true }
  apply empty T
  intro r hr c hc
  have ok := valid r hr c hc; have size : square F w (1+r) (1+c)<512 := (unpack _).1
  simp [T,cell,build,show r<B.rows+1 by omega,show C c<B.cols+1 by have := bd c hc; omega,size,ok]

theorem no_first_missing (u q i : Nat) (hi : 2≤ i ∧ i<q) (hq : q+2≤11+14*u)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (w : View)
    (allowed' : ∀ r≤6, ∀ c≤3*i+3, accepts (rowTag r) (realTag u c) (square F w (1+r) (1+c)) ∨
      (r=0 ∧ c=3*i+3 ∧ square F w (1+r) (1+c)=64))
    (before : ∀ t< i, marked F (L7.view w (35+42*u:Nat) 2 (2+3*t:Nat)))
    (missing : marked F (L7.view w (35+42*u:Nat) 2 (2+3*i:Nat))=false) : False := by
  let b := min i 4; let C := foldPre b i; let last := 3*i+3
  have hb : b=2 ∨ b=3 ∨ b=4 := by dsimp [b]; omega
  have bi : b<4 → b=i := by dsimp [b]; omega
  have bound (c : Nat) (hc : c≤last) : C c≤3*b+3 := by dsimp [last] at hc; unfold C foldPre; split_ifs <;> omega
  have track (c : Nat) : C c<3*b ↔ c<3*i := by unfold C foldPre; split_ifs <;> omega
  have target (c : Nat) : C c=3*b ↔ c=3*i := by unfold C foldPre; split_ifs <;> omega
  have stop (c : Nat) : C c=3*b+3 ↔ c=last := by unfold C foldPre last; split_ifs <;> omega
  have phase (c : Nat) : C c%3=c%3 := by unfold C foldPre; split_ifs <;> omega
  apply path_of_marks (last:=last) (preBox b) C F w (by simp [C,foldPre]) ((stop last).mpr rfl) bound _ (prefixOK b)
    (fun T => pre_false b (by simp; omega) T)
  swap
  · intro c _; have H : C (c+1)=C c+1 ∨ (b=4 ∧ C c=8 ∧ C (c+1)=6) := by unfold C foldPre; split_ifs <;> omega
    rcases H with h|⟨e,a,d⟩ <;> simp [pred,preBox, *]
  · intro r hr c hc; change r≤6 at hr
    let M := square F w (1+r) (1+c)
    change prefixOK b r (C c) M=true
    unfold prefixOK; apply Bool.and_eq_true_iff.mpr; constructor
    · rcases allowed' r hr c hc with A|⟨rfl,H,E⟩
      swap
      · exact Bool.or_eq_true_iff.mpr (.inr (by simp [M,E,(stop c).mpr H]))
      apply Bool.or_eq_true_iff.mpr; left; apply Bool.or_eq_true_iff.mpr
      by_cases far : 26+42*u≤c
      · right
        have last' : 3*i+3=27+42*u ∨ 3*i+3≤25+42*u := by omega
        have Cc : C c=c-3*(i-b) := by unfold C foldPre; split_ifs <;> omega
        have E : 8+(C c-(3*b+2))=realTag u c := by unfold realTag; dsimp [last] at hc; split_ifs <;> omega
        simp [show 3*b+2≤C c by dsimp [last] at hc; omega,E,M,A]
      · left
        have E : (if C c<5 then C c else 5+(1+C c)%3)=realTag u c := by unfold C foldPre realTag; split_ifs <;> omega
        rwa [E]
    · by_cases rr : r=0 <;> simp [rr]
      by_cases al : C c%3=0
      swap
      · simp [al]
      by_cases left : C c<3*b
      · have mark := before (c/3) (by have := phase c; have := (track c).mp left; omega)
        have m : marked F (L7.view w (35+42*u:Nat) 2 (2+c:Nat)) := by simpa only [show 3*(c/3)=c by have := phase c; omega] using mark
        have read' := cmask u c F w; simp [M,rr,read',left]; right; simpa using m
      · by_cases eq : C c=3*b
        · have m := (target c).mp eq; subst c; simp [M,rr,cmask,left]; right; simpa using missing
        · simp [show 3*b<C c by omega]
private theorem sibling_impossible (u q : Nat) (big : 3≤q)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic) (w : View)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a,patchSlack F a=0) (zero : ∀ p, coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (pre : ∀ i≤3+14*u, marked F (L7.view (turnView w) (35+42*u:Nat) 2 (2+3*i:Nat)))
    (start : marked F (L7.view (turnView w) (35+42*u:Nat) 2 2)) (second' : second F (turnView w))
    (end' : marked F (L7.view (turnView w) (35+42*u:Nat) 2 (32+42*u:Nat))=false) : False := by
  let v := turnView w; let C := foldSide u; let last := 30+42*u
  have tags (c : Nat) (hc : c≤last) : C c≤30 ∧ realTag 0 (C c)=realTag u c := by
    unfold C foldSide realTag; dsimp [last] at hc; split_ifs <;> omega
  apply path_of_marks (last:=last) sideBox C F v (by rfl) (by dsimp [C,last,foldSide,sideBox]; split_ifs <;> omega)
    (fun j hj => (tags j hj).1) _ sideOK side_false
  swap
  · intro c _; have h : C (c+1)=C c+1 ∨ (C c=11 ∧ C (c+1)=9) := by unfold C foldSide; split_ifs <;> omega
    rcases h with h|⟨a,b⟩ <;> simp [pred,sideBox, *]
  · intro r hr c hc; change r≤6 at hr
    unfold sideOK; apply Bool.and_eq_true_iff.mpr; constructor
    · rw [(tags c hc).2]; apply accept_physical u r c (by omega) (by omega) hc F acy P step v clean
      intro p hp; apply zero; rw [hp]; dsimp only [v]; rw [turned]; intro e
      cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at e <;> omega
    · by_cases rr : r=0
      swap
      · simp [rr]
      subst r; rw [cmask]; have c0 : C c=0 ↔ c=0 := by unfold C foldSide; split_ifs <;> omega
      have c3 : C c=3 ↔ c=3 := by unfold C foldSide; split_ifs <;> omega
      have c30 : C c=30 ↔ c=last := by dsimp [C,foldSide,last]; split_ifs <;> omega
      by_cases d : c=last
      · subst c; simp [last,v,show C last=30 from c30.mpr rfl,show 2+last=32+42*u by dsimp [last]; omega]; simpa using end'
      by_cases early : C c=0 ∨ C c=3 ∨ C c=6 ∨ C c=9
      · have idx : c%3=0 ∧ c/3≤3+14*u := by unfold C foldSide at early; split_ifs at early <;> omega
        have mark := pre (c/3) idx.2
        rw [show 3*(c/3)=c by omega] at mark
        simp [v,show C c≠30 from fun h => d (c30.mp h)]; right; simpa using mark
      · push_neg at early; simp [early,show C c≠30 from fun h => d (c30.mp h)]

private theorem all_of_first (u q : Nat) (hq : q+2≤11+14*u) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (w : View) (first : marked F (L7.view w (35+42*u:Nat) 2 2)) (second' : q>1 → second F w)
    (ok : ∀ i<q, ∀ r≤6, ∀ c≤3*i+3, accepts (rowTag r) (realTag u c) (square F w (1+r) (1+c)) ∨
      (r=0 ∧ c=3*i+3 ∧ square F w (1+r) (1+c)=64)) :
    ∀ i<q, marked F (L7.view w (35+42*u:Nat) 2 (2+3*i:Nat)) := by
  intro i; induction i using Nat.strong_induction_on with
  | h i ih =>
    intro lt
    rcases i with _|i
    · exact first
    rcases i with _|i
    · exact second' (by omega)
    by_contra no
    exact no_first_missing u q _ ⟨by omega,lt⟩ hq F w (ok _ lt) (fun t h => ih t h (by omega)) (Bool.eq_false_iff.mpr no)

/-- The depth-two centers preceding the star are forced without a bulk
axis assumption. Choosing the wrong arm at the elbow would run a prefix
into a closed corner on the uncharged side. -/
theorem west_teeth (u q : Nat) (odd : q%2=1) (hq : q+2≤11+14*u)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (w : View) (s f : Bool) (rim' : rim F w s f)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (clean : ∀ a,patchSlack F a=0) (zero : ∀ p, coord p≠L7.view w (35+42*(u:Int)) 2 (2+3*q:Nat) → starSlack F P p=0)
    (core : square F w 1 (1+3*q)=64) : ∀ i<q, marked F (L7.view w (35+42*u:Nat) 2 (2+3*i:Nat)) := by
  have first := gap_tooth u F acy clean w s f rim'
  apply all_of_first u q hq F w first
  · intro big; apply (has_second u F acy clean w s f rim').resolve_right; intro wrong
    have st : marked F (L7.view (turnView w) (35+42*u:Nat) 2 2) := by simpa [turned] using first
    have A (r c : Nat) (hr : r≤6) (hc : c≤30+42*u) : accepts (rowTag r) (realTag u c) (square F (turnView w) (1+r) (1+c)) := by
      apply accept_physical u r c (by omega) (by omega) hc F acy P step (turnView w) clean
      intro p hp; apply zero; rw [hp,turned]; intro e
      cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at e <;> omega
    have pre := all_of_first u (9+14*u) (by omega) F (turnView w) st (fun _ => wrong)
      (fun i hi r hr c hc => Or.inl (A r c hr (by omega)))
    exact sibling_impossible u q (by omega) F acy w P step clean zero (fun i hi => pre i (by omega)) st wrong
      (sibling_end u F acy score one clean w s f rim')
  · intro i hi r hr c hc
    by_cases E : r=0 ∧ c=3*q
    · obtain ⟨rfl,rfl⟩ := E; exact Or.inr ⟨rfl,by omega,core⟩
    left; apply accept_physical u r c (by omega) (by omega) (by omega) F acy P step w clean
    intro p hp; apply zero; rw [hp]; intro e
    cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [L7.view,reflect] at e <;> omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Teeth
