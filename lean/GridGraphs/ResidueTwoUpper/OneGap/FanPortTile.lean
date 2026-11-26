import GridGraphs.ResidueTwoUpper.OneGap.FanPortEncode
import GridGraphs.ResidueTwoUpper.OneGap.FanPortSpeed

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
open FanSlab

abbrev Marks := Nat → Nat → Bool
abbrev Arrows := Nat → Nat → Fin 4

def ink (M : Marks) (r c : Nat) : Ink := fun k => M (r+k.val/3) (c+k.val%3)
def dirs (A : Arrows) (r c : Nat) : Dir := fun k => A (r+k.val/3) (c+k.val%3)
def lab (M : Marks) (A : Arrows) (r c : Nat) := label (bits (ink M r c)) (dirs A r c)

def Across (M : Marks) (A : Arrows) (r c : Nat) := Own (A r c==0) (A r (c+1)==2) (M r c) (M r (c+1))
def Down (M : Marks) (A : Arrows) (r c : Nat) := Own (A r c==1) (A (r+1) c==3) (M r c) (M (r+1) c)

private theorem flipOwn (a b m n : Bool) : Own a b m n ↔ Own b a n m := by cases a <;> cases b <;> cases m <;> cases n <;> decide
private theorem tile_mem (M : Marks) (A : Arrows) (r c : Nat)
    (h : ∀ b<3, ∀ a<2, Across M A (r+b) (c+a)) (v : ∀ b<2, ∀ a<3, Down M A (r+b) (c+a)) :
    lab M A r c∈labels (bits (ink M r c)) := by
  apply label_mem; intro i; constructor
  · intro ne; apply (flipOwn ..).mpr
    have z := h (i.val/3) (by have := i.isLt; omega) (i.val%3-1) (by omega)
    simpa only [Across,dirs,ink,Fin.ofNat,show (i.val-1)%9=i.val-1 by have := i.isLt; omega,
      show (i.val-1)/3=i.val/3 by omega,show (i.val-1)%3=i.val%3-1 by omega,show c+(i.val%3-1)+1=c+i.val%3 by omega] using z
  · intro ge; apply (flipOwn ..).mpr
    have z := v (i.val/3-1) (by have := i.isLt; omega) (i.val%3) (by omega)
    simpa only [Down,dirs,ink,Fin.ofNat,show (i.val-3)%9=i.val-3 by have := i.isLt; omega,
      show (i.val-3)/3=i.val/3-1 by omega,show (i.val-3)%3=i.val%3 by omega,show r+(i.val/3-1)+1=r+i.val/3 by omega] using z

private theorem right_meet (M : Marks) (A : Arrows) (r c : Nat) (h : ∀ b<3, Across M A (r+b) (c+2)) : meets 0 (lab M A r c) (lab M A r (c+3)) := by
  apply meet_label _ _ _ _ 0 2 rfl; intro k; have z := h k.val k.isLt; fin_cases k <;> simpa [Across,dirs,ink,idx,Nat.add_assoc] using z
private theorem down_meet (M : Marks) (A : Arrows) (r c : Nat) (h : ∀ a<3, Down M A (r+2) (c+a)) : meets 1 (lab M A r c) (lab M A (r+3) c) := by
  apply meet_label _ _ _ _ 1 3 rfl; intro k; have z := h k.val k.isLt; fin_cases k <;> simpa [Down,dirs,ink,idx,Nat.add_assoc] using z

private theorem read_bit : ∀ f : Ink, ∀ i : Fin 9, (bits f).testBit i.val=f i := by native_decide

theorem corner_eq (M : Marks) (r c y x : Nat) (hy : y≤3) (hx : x≤3) :
    corner (bits (ink M r c)) (bits (ink M (r+3) c)) (bits (ink M r (c+3))) (bits (ink M (r+3) (c+3))) y x=bits (ink M (r+y) (c+x)) := by
  unfold corner; apply congrArg bits; funext k
  let Y := y+k.val/3; let X := x+k.val%3; let i : Fin 9 := ⟨3*(Y%3)+X%3,by omega⟩
  change Nat.testBit (if X<3 then if Y<3 then _ else _ else if Y<3 then _ else _) i.val=_
  have lo : i.val/3=Y%3 ∧ i.val%3=X%3 := by dsimp [i]; omega
  split_ifs <;> rw [read_bit _ i] <;> unfold ink <;> rw [lo.1,lo.2] <;> congr 1 <;> dsimp [X,Y] at * <;> have := k.isLt <;> omega

structure Inputs (W H : Nat) (dang : Bool) (M : Marks) (A : Arrows) : Prop where
  east : ∀ r<3*(H+1), ∀ c, c+1<3*(W+1) → Across M A r c
  south : ∀ r, r+1<3*(H+1) → ∀ c<3*(W+1), Down M A r c
  straight : ∀ j≤H, ∀ i≤W, bits (ink M (3*j) (3*i))∈shapes
  regular : ∀ j<H, ∀ i<W, ∀ b≤3, ∀ a≤3, accepts (5+(b+1)%3) (5+(a+1)%3) (bits (ink M (3*j+b) (3*i+a)))
  ray : ∀ j≤H, ∀ i<W, bits (ink M (3*j) (3*i))=73 → bits (ink M (3*j) (3*(i+1)))=73
  top : ∀ i≤W, bits (ink M 0 (3*i))=73 ∧ ∀ a : Fin 3, (A 0 (3*i+a.val)==3)=(if dang then false else a==0)

private theorem glue {W H} (L : Nat → Nat → Nat) (e : Bond) (he : e∈bonds W H) :
    let X := fun j i => Quad.mk (L j i) (L (j+1) i) (L j (i+1)) (L (j+1) (i+1))
    e.r<H ∧ e.c<W ∧ e.y<H ∧ e.x<W ∧ seam (X e.r e.c) e.s=seam (X e.y e.x) e.t := by
  simp [bonds,List.mem_flatMap,List.mem_map,List.mem_filterMap] at he
  rcases he with ⟨r,hr,c,hc,h,rfl⟩|⟨r,hr,c,hc,h,rfl⟩|⟨r,c,⟨hr,hc,h⟩,rfl⟩|⟨r,c,⟨hr,hc,h⟩,rfl⟩
  · exact ⟨hr,hc,hr,h,rfl⟩
  · exact ⟨hr,hc,h,hc,rfl⟩
  · exact ⟨hr,h,hr,hc,rfl⟩
  · exact ⟨h,hc,hr,hc,rfl⟩

set_option maxHeartbeats 700000 in
theorem replay_extra (extra : Nat → Nat → Nat → Nat → Bool) {W H d s k dang} (M : Marks) (A : Arrows) (I : Inputs W H dang M A)
    (extraOK : ∀ j<H, ∀ i<W, extra (bits (ink M (3*j) (3*i))) (bits (ink M (3*(j+1)) (3*i)))
      (bits (ink M (3*j) (3*(i+1)))) (bits (ink M (3*(j+1)) (3*(i+1)))))
    (test' : testWith (poolWith (fun a b c d => markOK a b c d && extra a b c d) (shapes.map fun m => (m,labels m))) W H d s k dang) (fit : s<H ∧ d<W) : ∀ j≤ s, bits (ink M (3*j) (3*d))=73 := by
  let L (j i : Nat) := lab M A (3*j) (3*i)
  let X (j i : Nat) := Quad.mk (L j i) (L (j+1) i) (L j (i+1)) (L (j+1) (i+1))
  have init (j i : Nat) (hj : j<H) (hi : i<W) : X j i∈poolWith (fun a b c d => markOK a b c d && extra a b c d) (shapes.map fun m => (m,labels m)) ∧ (j=0 → topOK dang (X j i)) := by
    let m (y x : Nat) := bits (ink M (3*y) (3*x))
    have memb (y x : Nat) (hy : y≤H) (hx : x≤W) : L y x∈labels (m y x) := tile_mem M A _ _ (fun b hb a ha => I.east _ (by omega) _ (by omega)) (fun b hb a ha => I.south _ (by omega) _ (by omega))
    have rt (y x : Nat) (hy : y≤H) (hx : x<W) : meets 0 (L y x) (L y (x+1)) := by
      dsimp [L]; rw [show 3*(x+1)=3*x+3 by omega]; exact right_meet M A _ _ (fun b hb => I.east _ (by omega) _ (by omega))
    have dn (y x : Nat) (hy : y<H) (hx : x≤W) : meets 1 (L y x) (L (y+1) x) := by
      dsimp [L]; rw [show 3*(y+1)=3*y+3 by omega]; exact down_meet M A _ _ (fun a ha => I.south _ (by omega) _ (by omega))
    constructor
    · apply in_pool (fun a b c d => markOK a b c d && extra a b c d) (I.straight _ (by omega) _ (by omega)) (I.straight _ (by omega) _ (by omega)) (I.straight _ (by omega) _ (by omega)) (I.straight _ (by omega) _ (by omega))
        (memb j i (by omega) (by omega)) (memb (j+1) i (by omega) (by omega)) (memb j (i+1) (by omega) (by omega)) (memb (j+1) (i+1) (by omega) (by omega)) _ (dn _ _ hj (by omega)) (rt _ _ (by omega) hi) (rt _ _ (by omega) hi) (dn _ _ hj (by omega))
      apply Bool.and_eq_true_iff.mpr; refine ⟨?_,extraOK j hj i hi⟩
      unfold markOK; simp only [Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq,List.all_eq_true,List.mem_range]; refine ⟨⟨or_iff_not_imp_left.mpr ?_,or_iff_not_imp_left.mpr ?_⟩,?_⟩
      · simpa using I.ray j (by omega) i hi
      · simpa using I.ray (j+1) (by omega) i hi
      · intro r hr c hc; rw [show 3*(i+1)=3*i+3 by omega,show 3*(j+1)=3*j+3 by omega,corner_eq _ _ _ _ _ (by omega) (by omega)]; exact I.regular _ hj _ hi _ (by omega) _ (by omega)
    · rintro rfl
      have top (x) (hx : x≤W) : mask (L 0 x)=73 ∧ out (L 0 x) 3=(if dang then 0 else 1) := by
        obtain ⟨e,ar⟩ := I.top x hx; change mask (label _ _)=73 ∧ out (label _ _) ((3:Fin 4).val)=_; rw [mask_label,port_label]; refine ⟨e,?_⟩
        have a0 := ar 0; have a1 := ar 1; have a2 := ar 2
        unfold three; dsimp [dirs,idx]; cases dang <;> simp_all
        simp [Bool.eq_false_iff.mpr (fun h => a1 (beq_iff_eq.mp h)),Bool.eq_false_iff.mpr (fun h => a2 (beq_iff_eq.mp h))]
      simp [topOK,X,top _ (Nat.le_of_lt hi),top _ (show i+1≤W by omega)]
  have pass := window_with (W:=W) (H:=H) (d:=d) (s:=s) (rounds:=k) (dang:=dang) X (fun r hr c hc => init r c hr hc) (glue L) test' fit
  intro j hj; exact (mask_label _ _).symm.trans (pass _ hj)
theorem replay_window {W H d s k dang} (M : Marks) (A : Arrows) (I : Inputs W H dang M A)
    (test' : test W H d s k dang) (fit : s<H ∧ d<W) : ∀ j≤ s, bits (ink M (3*j) (3*d))=73 := by
  apply replay_extra (d:=d) (s:=s) (k:=k) (fun _ _ _ _ => true) M A I (fun _ _ _ _ => rfl) _ fit
  have eq : (fun a b c d => markOK a b c d && true)=markOK := by funext a b c d; simp
  rw [eq]; change test W H d s k dang=true; exact test'
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
