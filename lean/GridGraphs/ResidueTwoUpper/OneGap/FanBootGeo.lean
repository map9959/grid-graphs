import GridGraphs.ResidueTwoUpper.OneGap.FanBootData
import GridGraphs.ResidueTwoUpper.OneGap.FanStep

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil L7 FanSlab

theorem accept_bulk (u r c : Nat) (hu : r+8≤33+42*u) (hc : c≤30+42*u)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (w : View) (clean : ∀ a,patchSlack F a=0)
    (zs : ∀ p, coord p=L7.view w (35+42*(u:Int)) (r+2:Nat) (c+2:Nat) → starSlack F P p=0) :
    accepts (rowTag r) (realTag u c) (square F w (1+r) (1+c)) := by
  let n := 35+42*u
  let a := onSite (s:=n-2) (L7.view w (33+42*(u:Int)) (1+r:Nat) (1+c:Nat)) (by
    rw [show n-2=33+42*u by dsimp [n]; omega]; exact_mod_cast inside_view (n:=33+42*u) w (by omega : 1+r<_) (by omega : 1+c<_))
  have ha : coord a=L7.view w (33+42*(u:Int)) (1+r:Nat) (1+c:Nat) := coord_onSite ..
  let p := onSite (s:=n) (L7.view w (35+42*(u:Int)) (r+2:Nat) (c+2:Nat)) (by
    dsimp [n]; exact_mod_cast inside_view (n:=35+42*u) w (by omega : r+2<_) (by omega : c+2<_))
  have hp : coord p=L7.view w (35+42*(u:Int)) (r+2:Nat) (c+2:Nat) := coord_onSite ..
  have xy : coord p=coord a+(1,1) := by
    rw [hp,ha,show (33+42*(u:Int))=35+42*(u:Int)-2 by ring,view_center]; push_cast; congr 1 <;> ring
  obtain ⟨em,en⟩ := PatchFilter.packed_center F a p xy
  let m := maskAt F a
  let o : Fin 5 := ⟨outDir p (P p),outDir_lt ..⟩
  let Z := L7.view w 33 (rowTag r+1:Nat) (small (realTag u c))
  have rt : rowTag r<8 := by unfold rowTag; split <;> omega
  have ct : realTag u c<13 := by unfold realTag; split_ifs <;> omega
  have hZ : inside 33 Z := inside_view (n:=33) w (by omega) (by unfold small; split <;> omega)
  have ins (d : Nat) : inside 35 (shift (Z+(1,1)) d) := by simp [inside] at hZ; unfold shift; split <;> simp [inside] <;> omega
  have S := starOK_physical F acy p _ (fun h => step _ h.symm)
  rw [←em,←en] at S
  have ok : starOK 35 (Z+(1,1)) (bit m 4) (PatchFilter.cnb m) o := by
    unfold starOK at S ⊢; simp only [ins,Bool.true_and,Bool.and_eq_true,Bool.or_eq_true,List.all_eq_true] at *
    exact ⟨fun d hd => (S.1 _ hd).imp_right And.right,S.2.imp_right And.right⟩
  have R : related u (1+r) (rowTag r+1) := by unfold related rowTag; split <;> omega
  have C : related u (1+c) (small (realTag u c)) := by simpa [Nat.add_comm] using along u c
  have co := agreements R C w m (bit m 4) (PatchFilter.cnb m) o
  have N : ((35+42*u:Nat):Int)=35+42*(u:Int) := by push_cast; ring
  have za := clean a
  change twoOrbitPatch ((35+42*u:Nat):Int) (coord a) m=0 at za
  rw [N,ha] at za
  have z1 : twoOrbitPatch 35 Z m=0 := co.1.symm.trans za
  have zp := zs p hp
  change twoOrbitStar ((35+42*u:Nat):Int) (coord p) _ _ _=0 at zp
  rw [←em,←en,N,xy,ha,show (33+42*(u:Int))=35+42*(u:Int)-2 by ring,view_center] at zp
  have z2 : twoOrbitStar 35 (Z+(1,1)) (bit m 4) (PatchFilter.cnb m) o=0 := by
    have ze : Z+(1,1)=_ := view_center w 35 (rowTag r+1:Nat) (small (realTag u c))
    rw [ze]; exact co.2.symm.trans zp
  have H := entry_ok w ⟨_,rt⟩ ⟨_,ct⟩ m
  change (!maskOK m || accepts (rowTag r) (realTag u c) (encode m w) || twoOrbitPatch 35 Z m != 0 || (List.range 5).all _)=true at H
  have yes : maskOK m := physical_mask_ok F acy ..
  simp only [yes,Bool.not_true,Bool.false_or,z1,bne_self_eq_false,Bool.or_false,Bool.or_eq_true,List.all_eq_true] at H
  rw [square_eq F w _ _ a (by rw [ha,N]; congr 1 <;> ring)]
  rcases H with pass|bad
  · exact pass
  · have h := bad o (List.mem_range.mpr o.isLt)
    change (!starOK 35 (Z+(1,1)) _ _ o)=true ∨ (twoOrbitStar 35 (Z+(1,1)) _ _ o != 0)=true at h
    simp [ok,z2] at h
theorem accept_physical (u r c : Nat) (hu : r+8≤33+42*u) (_hr : r≤27) (hc : c≤30+42*u)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ p,P p≠p → (Bonds F).Adj p (P p))
    (w : View) (clean : ∀ a,patchSlack F a=0)
    (zs : ∀ p, coord p=L7.view w (35+42*(u:Int)) (r+2:Nat) (c+2:Nat) → starSlack F P p=0) :
    accepts (rowTag r) (realTag u c) (square F w (1+r) (1+c)) :=
  accept_bulk u r c hu hc F acy P step w clean zs
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
