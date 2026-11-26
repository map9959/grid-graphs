import GridGraphs.ResidueTwoUpper.OneGap.FanGapTooth
import GridGraphs.ResidueTwoUpper.OneGap.FanRootTransport

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open L7 ResidueZero Stencil BoundarySix.Connected TwoGap.Words GridGraphs.ResidueTwoUpper.Exceptional.Frame

def second {n} (F : Finset (GridVertex n n)) (w : View) := marked F (L7.view w n 2 5)
private def opts (s f : Bool) (c : Nat) := (opt s f c).filter fun m => (c != 2 || lane m 5==0) && (c != 5 || lane m 2==0)
private def reach (s f : Bool) : Nat → List (Nat × Nat)
  | 0 => (opts s f 0).flatMap fun a => (opts s f 1).map fun b => (a,b)
  | j+1 => ((reach s f j).flatMap fun (a,b) => ((opts s f (j+2)).filter (FanSeed.cleanBand j a b)).map fun c => (b,c)).eraseDups
private theorem elbow_no : ∀ s f, (reach s f 5).isEmpty := by native_decide

theorem has_second (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (clean : ∀ a,patchSlack F a=0) (w : View) (s f : Bool) (side : rim F w s f) : second F w ∨ second F (turnView w) := by
  by_contra! no
  let X := chartCol F w
  have choices (c : Nat) (hc : c<7) : X c∈opts s f c := by
    have C := column_of_rim F w s f side c (by omega)
    have eq (r : Nat) : preset (35+42*u) s f r c=preset 35 s f r c := by unfold preset; split_ifs <;> first | rfl | omega
    have op : X c∈opt s f c := List.mem_filter.mpr ⟨List.mem_range.mpr (col_lt ..),by simpa only [columnOK,eq] using C⟩
    apply List.mem_filter.mpr; refine ⟨op,?_⟩
    have b := col_bit F w (5 : Fin 7) 2; have a := col_bit F w (2 : Fin 7) 5
    simp only [second,turned,Bool.not_eq_true] at no
    change lane (X 2) 5=(marked F (L7.view w _ 5 2)).toNat at b
    change lane (X 5) 2=(marked F (L7.view w _ 2 5)).toNat at a
    simp [no.1,no.2] at a b
    by_cases h : c=2 <;> by_cases k : c=5 <;> simp_all
  have in' (j : Nat) (hj : j≤5) : (X j,X (j+1))∈reach s f j := by
    induction j with
    | zero => exact List.mem_flatMap.mpr ⟨_,choices _ (by decide),List.mem_map.mpr ⟨_,choices _ (by decide),rfl⟩⟩
    | succ j ih =>
      rw [reach,List.mem_eraseDups,List.mem_flatMap]; refine ⟨_,ih (by omega),List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨choices _ (by omega),?_⟩,rfl⟩⟩
      simpa only [fold,show j<21 by omega,if_true] using physical u F acy clean w j (by omega)
  simpa [List.isEmpty_iff.mp (elbow_no s f)] using in' 5 le_rfl

def back (w : View) := turnView (opposite (turnView w))
theorem back_pos (w : View) (n r c : Int) : L7.view (back w) n r c=L7.view w n r (n-1-c) := by simp [back,turned,opposite_pos]
private theorem end_closed {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (cm : ∀ x,isCorner x → x∈F)
    (ln : ∀ x,straight n (coord x) → x∈F) (one : (perimeterHoles F).card=1) (w : View) (s f : Bool) (side : rim F w s f) :
    ∀ b, (otherEnd (turnView w),b)∉gaps hn F := by
  let t := if s then !w.swap else w.swap
  have un (i : Fin 3) (hi : i.val=1 ∨ i.val=2) : (atArm hn (corner w,t) i).1∉F := by
    have E : coord (atArm hn (corner w,t) i).1=L7.view w n (if s then (i.val:Int) else 0) (if s then 0 else (i.val:Int)) := by
      cases w with | mk x y z => cases x <;> cases y <;> cases z <;> cases s <;> ext <;> simp [corner,t,coord,atArm,loc,L7.view,reflect] <;> omega
    have Z : marked F (coord (atArm hn (corner w,t) i).1)=false := by
      rw [E]; cases s
      · exact side 0 i.val (by decide) (by omega) false (by simp [preset,hi])
      · exact side i.val 0 (by omega) (by omega) false (by simp [preset,hi,show i.val≠0 by omega])
    simpa [marked_at] using Z
  rw [exact_holes hn F cm ln,Finset.card_image_of_injective _ (gapEdge_inj hn)] at one
  have G : (corner w,t)∈gaps hn F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,un 1 (.inl rfl),un 2 (.inr rfl)⟩
  have ne : otherEnd (turnView w)≠corner w := by cases w with | mk a b s => cases a <;> cases b <;> cases s <;> decide
  intro b H; apply ne; obtain ⟨a,eq⟩ := Finset.card_eq_one.mp one
  rw [eq,Finset.mem_singleton] at H G; exact congrArg Prod.fst (H.trans G.symm)

private theorem last_preset (u : Nat) (f : Bool) (k : Fin 9) (hk : k.val≠8) :
    preset (35+42*u) false f (k.val/3) (35+42*u-1-k.val%3)=some ((preset 35 false f (k.val/3) (34-k.val%3)).getD false) := by
  have eq : preset (35+42*u) false f (k.val/3) (35+42*u-1-k.val%3)=preset 35 false f (k.val/3) (34-k.val%3) := by
    unfold preset; split_ifs <;> first | rfl | omega
  rw [eq]; fin_cases k <;> cases f <;> first | rfl | contradiction | (norm_num at hk)


set_option maxHeartbeats 1200000 in
/-- Both marked feet at a closed corner preclude its common depth-two tooth. -/
theorem sibling_end (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) (one : (perimeterHoles F).card=1) (clean : ∀ a,patchSlack F a=0)
    (w : View) (s f : Bool) (side : rim F w s f) : marked F (L7.view (turnView w) (35+42*u:Nat) 2 (32+42*u:Nat))=false := by
  let v := turnView w
  have hn : 35≤35+42*u := by omega
  obtain ⟨P,_,step,_,_,_,good,_⟩ := frame_of_score u F acy score
  have geo (p) := star_geometry hn F P step p (good (.inl p))
  have cm := corners_marked u F acy score; have ln := fun p => (geo p).1
  obtain ⟨g,hs⟩ := realize_on hn F v false (fun j => 3≤j) cm ln (fun p => (geo p).2.1)
    (fun i _ h => by have := i.isLt; omega) (fun _ _ h => by omega) (end_closed hn F cm ln one w s f side) (physicalWord_ok hn F P good _)
  let n := 35+42*u; let a := onSite (s:=n-2) (L7.view (back v) (33+42*(u:Int)) 0 0) (by
    rw [show n-2=33+42*u by dsimp [n]; omega]; exact_mod_cast inside_view (n:=33+42*u) (r:=0) (j:=0) (back v) (by omega) (by omega))
  have ha : coord a=L7.view (back v) (33+42*(u:Int)) 0 0 := coord_onSite ..
  have z := clean a; change twoOrbitPatch ((35+42*u:Nat):Int) (coord a) _=0 at z
  rw [ha] at z; push_cast at z
  have same := samePatch (back v) u 0 0 (by decide) (maskAt F a)
  simp only [Nat.cast_zero,fold,show 0<21 by decide,if_true] at same
  have E := FanSlab.square_eq F (back v) 0 0 a (by rw [ha]; push_cast; congr 1 <;> ring)
  have bit' (k : Fin 9) : lane (encode (maskAt F a) (back v)) k=(marked F (L7.view v n (k.val/3:Nat) (n-1-(k.val%3):Nat))).toNat := by
    rw [←E]; unfold FanSlab.square; rw [(FanSlab.unpack _).2 k]; simp only [Nat.zero_add,back_pos]; have d : ((n-1-k.val%3:Nat):Int)=(n:Int)-1-(k.val%3:Nat) := by dsimp [n]; omega
    rw [d]
  have chk : ∀ (W : View) (m : Fin 512) (f : Bool), maskOK m → twoOrbitPatch 35 (L7.view W 33 0 0) m=0 →
      (∀ k : Fin 9, k.val≠8 → lane (encode m W) k=((preset 35 false f (k.val/3) (34-k.val%3)).getD false).toNat) → lane (encode m W) 8=0 := by native_decide
  have out := chk (back v) (maskAt F a) g (physical_mask_ok F acy ..) (same.symm.trans z) (by
    intro k hk; rw [bit']; apply congrArg Bool.toNat; apply hs _ _ (by dsimp [n]; omega) (by omega) (by dsimp [n]; omega)
    exact last_preset u g k hk)
  change lane (encode _ (back v)) ((8:Fin 9).val)=0 at out; rw [bit'] at out
  change (marked F (L7.view v n 2 (n-1-2:Nat))).toNat=0 at out
  rw [show n-1-2=32+42*u by dsimp [n]; omega] at out; simpa [v,n] using out
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
