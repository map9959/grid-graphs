import GridGraphs.ResidueTwoUpper.OneGap.FanSlabChartCheck

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSlab
open ResidueZero Stencil L7

def realTag (u c : Nat) := if c<5 then c else if 26+42*u≤c then 8+(c-(26+42*u)) else 5+((c+1)%3)
def related (u a b : Nat) : Prop := (a=b ∧ b≤5) ∨ (a=b+42*u ∧ 27≤b) ∨
  (6≤a ∧ a+7≤33+42*u ∧ 6≤b ∧ b≤8 ∧ a%3=b%3)
theorem along (u c : Nat) : related u (c+1) (small (realTag u c)) := by
  unfold related small realTag; split_ifs <;> omega
private theorem across (u top r : Nat) (hm : top%3=1) (lo : 6≤top) (hi : top+19≤33+42*u) (hr : r<13) :
    related u (top+r) (6+(1+r%3)%3) := by unfold related; omega
set_option maxHeartbeats 1500000 in
private theorem axis' {u a b : Nat} (h : related u a b) (δ t : Int) (dt : δ=2 ∧ t=0 ∨ δ=0 ∧ t=1) (f : Bool) :
    rep (23-δ) (4+14*(u:Int)) (reflect f (35+42*(u:Int)-δ) ((a:Int)+t))=
    rep (23-δ) 4 (reflect f (35-δ) ((b:Int)+t)) := by
  unfold related at h; rcases dt with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases f <;>
    unfold reflect rep <;> split_ifs <;> omega
private theorem chart {u r c a b : Nat} (R : related u r a) (C : related u c b) (w : View)
    (δ t : Int) (dt : δ=2 ∧ t=0 ∨ δ=0 ∧ t=1) :
    representative (23-δ) (4+14*(u:Int)) (L7.view w (35+42*(u:Int)-δ) (r+t) (c+t))=
    representative (23-δ) 4 (L7.view w (35-δ) (a+t) (b+t)) := by
  cases w with | mk x y s => cases s <;> apply Prod.ext <;> first | exact axis' R _ _ dt _ | exact axis' C _ _ dt _
theorem agreements {u r c a b : Nat} (R : related u r a) (C : related u c b) (w : View) (m f nb o : Nat) :
    twoOrbitPatch (35+42*(u:Int)) (L7.view w (33+42*(u:Int)) r c) m = twoOrbitPatch 35 (L7.view w 33 a b) m ∧
    twoOrbitStar (35+42*(u:Int)) (L7.view w (35+42*(u:Int)) ((r:Int)+1) ((c:Int)+1)) f nb o =
      twoOrbitStar 35 (L7.view w 35 ((a:Int)+1) ((b:Int)+1)) f nb o := by
  have p := chart R C w 2 0 (.inl ⟨rfl,rfl⟩)
  have s := chart R C w 0 1 (.inr ⟨rfl,rfl⟩)
  norm_num at p s
  rw [show 35+42*(u:Int)-2=33+42*(u:Int) by ring] at p
  constructor
  · let loc := L7.view w (33+42*(u:Int)) r c
    change twoOrbitPatch _ loc _=_
    simp only [twoOrbitPatch,show 35+42*(u:Int)-2=21+3*(4+14*(u:Int)) by ring,
      show (35:Int)-2=21+3*4 by decide,patchLocation_transport (b:=21) (by decide) (j:=4+14*(u:Int)) (by positivity),
      patchLocation_transport (b:=21) (by decide) (j:=4) (by decide),loc,p]
  · let loc := L7.view w (35+42*(u:Int)) ((r:Int)+1) ((c:Int)+1)
    let z := L7.view w 35 ((a:Int)+1) ((b:Int)+1)
    have ll (g : Nat) : starLocation (35+42*(u:Int)) (image (35+42*(u:Int)) g loc)=starLocation 35 (image 35 g z) := by
      rw [show 35+42*(u:Int)=23+3*(4+14*(u:Int)) by ring,starLocation_transport (by decide : (19:Int)≤23) (by positivity)]
      exact (congrArg (fun q => starLocation 23 (image 23 g q)) s).trans
        (starLocation_transport (b:=23) (by decide) (j:=4) (by decide) z g).symm
    change twoOrbitStar _ loc _ _ _=twoOrbitStar _ z _ _ _; simp only [twoOrbitStar,ll]

theorem mask_rule (u top r c : Nat) (lo : 6≤top) (hi : top+19≤33+42*u) (hm : top%3=1)
    (hr : r<13) (hc : c≤30+42*u) (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → _) (step : ∀ x, P x≠x → (Bonds F).Adj x (P x)) (w : View)
    (a : origins (35+42*u)) (ha : coord a=L7.view w (33+42*(u:Int)) (top+r:Nat) (c+1:Nat))
    (p : GridVertex (35+42*u) (35+42*u)) (hp : coord p=coord a+(1,1))
    (clean : patchSlack F a=0) (zs : starSlack F P p=0) :
    words[13*(r%3)+realTag u c]!.testBit (encode (maskAt F a) w) := by
  let m := maskAt F a
  let t := realTag u c
  let z := L7.view w 33 (6+(1+r%3)%3:Nat) (small t)
  have ht : t<13 := by dsimp [t,realTag]; split_ifs <;> omega
  have hz : inside 33 z := inside_view (n:=33) w (by omega) (by unfold small; split <;> omega)
  let o : Fin 5 := ⟨outDir p (P p),outDir_lt ..⟩
  obtain ⟨em,en⟩ := PatchFilter.packed_center F a p hp
  have st := starOK_physical F acy p _ (fun h => step _ h.symm)
  rw [←em,←en] at st
  have ins (d : Nat) : inside 35 (shift (z+(1,1)) d) := by
    simp [inside] at hz; unfold shift; split <;> simp [inside] <;> omega
  have ok : starOK 35 (z+(1,1)) (bit m 4) (PatchFilter.cnb m) o := by
    unfold starOK at st ⊢
    simp only [ins,Bool.true_and,Bool.and_eq_true,Bool.or_eq_true,List.all_eq_true] at *
    exact ⟨fun d hd => (st.1 _ hd).imp_right And.right,st.2.imp_right And.right⟩
  have co := agreements (across u top r hm lo hi hr) (along u c) w m (bit m 4) (PatchFilter.cnb m) o
  change twoOrbitPatch ((35+42*u:Nat):Int) (coord a) m=0 at clean
  change twoOrbitStar ((35+42*u:Nat):Int) (coord p) _ _ _=0 at zs
  rw [←em,←en,hp,ha] at zs
  rw [ha] at clean
  have N : ((35+42*u:Nat):Int)=35+42*(u:Int) := by push_cast; ring
  rw [N] at clean zs
  have price : twoOrbitPatch 35 z m=0 := co.1.symm.trans clean
  have S : twoOrbitStar 35 (z+(1,1)) (bit m 4) (PatchFilter.cnb m) o=0 := by
    have e : z+(1,1)=_ := view_center w 35 (6+(1+r%3)%3:Nat) (small t)
    rw [e]; apply co.2.symm.trans
    rw [show (33+42*(u:Int))=35+42*(u:Int)-2 by ring,view_center] at zs; exact zs
  have H := lookup w ⟨r%3,by omega⟩ ⟨t,ht⟩ m
  change (!maskOK m || words[13*(r%3)+t]!.testBit (encode (Fin.ofNat 512 m.val) w) ||
    twoOrbitPatch 35 z m != 0 || (List.range 5).all _)=true at H
  have yes : maskOK m := physical_mask_ok F acy ..
  simp only [yes,Bool.not_true,Bool.false_or,price,bne_self_eq_false,Bool.or_false,Bool.or_eq_true,List.all_eq_true] at H
  rcases H with y|bad
  · simpa using y
  · have h := bad o (List.mem_range.mpr o.isLt)
    change (!starOK 35 (z+(1,1)) _ _ o)=true ∨ (twoOrbitStar 35 (z+(1,1)) _ _ o != 0)=true at h
    simp [ok,S] at h
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSlab
