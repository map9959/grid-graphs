import GridGraphs.ResidueTwoUpper.StencilUpper

/-! First obstruction on `35+42u`. A forest attaining the rounded LP
bound spends exactly 1/14 on local slacks. In particular the distinguished
corner is the only possible corner sink. Slacks are in the integral units
of the eight-view stencil (so multiply a score by `8*scale`). -/
namespace GridGraphs.ResidueTwoUpper.Stencil
open GridGraphs.ResidueZero hiding scale starNormPrices patchNormPrices edgePrices incidencePrices overlapPrices cornerPrices
open Finset

def starSlack {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (x : GridVertex n n) :=
  twoOrbitStar n (coord x) (decide (x∈F)).toNat (neighbours F (coord x)) (outDir x (P x))
def patchSlack {n} (F : Finset (GridVertex n n)) (x : origins n) :=
  twoOrbitPatch n (coord x) (maskAt F x)
def cornerBill {n} (P : GridVertex n n → GridVertex n n) (x : GridVertex n n) :=
  twoCornerAt n (coord x) (outDir x (P x))

theorem exact_ledger {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (covers : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) :
    (∑ x, starSlack F P x)+(∑ x, patchSlack F x) +
      (8*cornerPrices.getD 0 0 - ∑ x, cornerBill P x) =
        8*rhs n-8*scale*(F.card:Int) := by
  have h := physical_marginals_zero hn F P step covers
  unfold twoMarginalSum at h
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,sum_mark,twoNormAt_sum] at h
  unfold starSlack patchSlack maskAt cornerBill rhs
  linarith only [h]

private theorem bill_multiple (n : Nat) (p : Pos) (o : Nat) : (13689007128:Int) ∣ twoCornerAt n p o := by
  have each (g : Nat) : (13689007128:Int) ∣ 4*cornerPrices.getD (atPos n 6 (image n g p)) 0 := by
    rw [corner_price]; split_ifs <;> decide
  unfold twoCornerAt; split_ifs
  · simp only [show List.range 8=[0,1,2,3,4,5,6,7] by decide,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil]
    repeat apply dvd_add <;> first | exact each _ | exact dvd_zero _ | skip
  · exact dvd_zero _

def isCorner {n} (v : GridVertex n n) :=
  (v.1.val=0 ∨ v.1.val+1=n) ∧ (v.2.val=0 ∨ v.2.val+1=n)

private theorem corner_sink_price {n} (hn : 12≤n) (P : GridVertex n n → GridVertex n n)
    (v : GridVertex n n) (corner : isCorner v) (sink : P v=v) :
    cornerBill P v= -27378014256 := by
  have lo : axis n 6 0=0 := by unfold axis; split_ifs <;> omega
  have hi : axis n 6 ((n:Int)-1)=14 := by unfold axis; split_ifs <;> omega
  have dims (i : Fin n) (h : i.val=0 ∨ i.val+1=n) :
      (i.val:Int)=0 ∨ (i.val:Int)=(n:Int)-1 := by omega
  obtain row|row := dims v.1 corner.1 <;> obtain col|col := dims v.2 corner.2 <;>
    simp [cornerBill,sink,outDir,twoCornerAt,coord,row,col,
      show List.range 8=[0,1,2,3,4,5,6,7] by decide,corner_price,ResidueZero.image,atPos,lo,hi]

theorem exceptional_slack (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    let n := 35+42*u
    let root : GridVertex n n := (⟨0,by dsimp [n]; omega⟩,⟨0,by dsimp [n]; omega⟩)
    ∃ P : GridVertex n n → GridVertex n n, P root=root ∧
      (∀ v, P v≠v → (Bonds F).Adj v (P v)) ∧
      (∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) ∧
      (∀ v, v≠root → cornerBill P v=0) ∧
      (∀ v, isCorner v → P v=v → v=root) ∧
      (∑ x, starSlack F P x)+(∑ x, patchSlack F x)=3042001584 := by
  dsimp only
  let n := 35+42*u
  let root : GridVertex n n := (⟨0,by dsimp [n]; omega⟩,⟨0,by dsimp [n]; omega⟩)
  obtain ⟨P,sink,step,covers⟩ := parent_exists F root acy
  refine ⟨P,sink,step,covers,?_⟩
  let t := 5+14*u
  have e : n=20+3*t := by dsimp [n,t]; omega
  have ei : (n:Int)=20+3*(t:Int) := by exact_mod_cast e
  have ep : ((n-2:Nat):Int)=18+3*(t:Int) := by omega
  have st (v : GridVertex n n) : 0 ≤ starSlack F P v := by
    unfold starSlack; rw [ei]
    exact star_nonneg_of_check checkStars t (ei ▸ coord_inside v)
      (by cases decide (v∈F) <;> decide) (code_lt _) (outDir_lt ..)
      (ei ▸ starOK_physical F acy v _ (fun h => step _ h.symm))
  have pt (v : origins n) : 0≤patchSlack F v := by
    unfold patchSlack; rw [ei]
    exact patch_nonneg_of_check checkPatches t (ep ▸ coord_inside v)
      (Fin.isLt _) (physical_mask_ok F acy ..)
  have S := Finset.sum_nonneg (s:=univ) (fun x _ => st x)
  have M := Finset.sum_nonneg (s:=univ) (fun x _ => pt x)
  have cb (v : GridVertex n n) : cornerBill P v≤0 := corner_nonpos ..
  have cr : cornerBill P root=8*cornerPrices.getD 0 0 := by
    unfold cornerBill; rw [sink]; simpa [root,coord,outDir] using root_charge (n:=n) (by dsimp [n]; omega)
  let rem := univ.erase root
  have split := sum_erase_add (s:=univ) (mem_univ root) (f:=cornerBill P)
  have h := exact_ledger (n:=n) (by dsimp [n]; omega) F P step covers
  rw [←split,cr] at h
  have b := budget t
  rw [←e] at b
  have price : 8*rhs n-8*scale*(F.card:Int)=3042001584 := by
    rw [score]; dsimp [t] at b; push_cast at b ⊢; unfold scale at b ⊢
    ring_nf at b ⊢
    omega
  rw [price] at h
  have vanish (v : GridVertex n n) (ne : v≠root) : cornerBill P v=0 := by
    have mem : v∈rem := mem_erase.mpr ⟨ne,mem_univ _⟩
    have le := single_le_sum (s:=rem) (f:=fun x => -cornerBill P x)
      (fun x _ => neg_nonneg.mpr (cb x)) mem
    rw [sum_neg_distrib] at le
    obtain ⟨z,hz⟩ := bill_multiple n (coord v) (outDir v (P v))
    change cornerBill P v=_ at hz
    dsimp [rem] at le
    have hz' := cb v
    omega
  refine ⟨vanish,?_,?_⟩
  · intro v corner fixed
    by_contra ne
    have zero := vanish v ne
    have neg := corner_sink_price (n:=n) (by dsimp [n]; omega) P v corner fixed
    omega
  have empty : (∑ v ∈ rem, cornerBill P v)=0 :=
    sum_eq_zero fun v hv => vanish v (mem_erase.mp hv).1
  change (∑ v ∈ univ.erase root, cornerBill P v)=0 at empty
  rw [empty,zero_add,sub_self,add_zero] at h
  exact h

end GridGraphs.ResidueTwoUpper.Stencil
