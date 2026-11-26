import GridGraphs.FiniteOne.Stencil
import GridGraphs.ResidueZero.PhysicalPatch

namespace GridGraphs.FiniteOne
open ResidueZero Finset

private theorem turn0 (i : Fin 4) : turn 0 i=i := by fin_cases i <;> rfl
private theorem out0 (i : Fin 5) : turnOut 0 i=i := by fin_cases i <;> rfl
private theorem rot0 (i : Fin 512) : rotMask 0 i=i := by revert i; native_decide
private theorem bits0 (i : Fin 16) : rotBits 0 i=i := by revert i; decide +kernel
private theorem q0 (q : Fin 9) : patchQ 0 q=q := by revert q; decide +kernel
private theorem bond_flip (T : Prices) {s base} {p q : GridVertex s s} (d : Fin 2) (w : Nat)
    (h : shift (coord p) d=coord q) : bond T base s (coord p) d w= -bond T base s (coord q) (d+2) w := by
  have rev : shift (coord q) (d+2)=coord p := by rw [←h]; exact (reverse_step _ d).1
  unfold bond; simp [h,rev,coord_inside,d.isLt,show ¬d.val+2<2 by omega]

def pricedMax (T : Prices) (n : Nat) (p : Pos) (y : Int) :=
  (univ : Finset Atom).sup' univ_nonempty fun a =>
    if allowed n p a then starCost T n p a.1 a.2.1 a.2.2-y*a.1.val else bottom
def pricedBudget (T : Prices) (n : Nat) (y : Pos → Int) :=
  (∑ v : GridVertex n n, pricedMax T n (coord v) (y (coord v))) + ∑ a : origins n, patchMax T n (coord a)

set_option maxHeartbeats 800000 in
theorem charged_sound {n} (hn : 2≤n) (T : Prices) (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic)
    (y : Pos → Int) : (T.unit:Int)*F.card - (∑ v : GridVertex n n, y (coord v)*(decide (v∈F)).toNat) ≤
      pricedBudget T n y := by
  let root : GridVertex n n := (⟨0,by omega⟩,⟨0,by omega⟩)
  obtain ⟨P,sink,step,covers⟩ := parent_exists F root acy
  let f (v : GridVertex n n) := (decide (v∈F)).toNat
  let nb (v : GridVertex n n) := neighbours F (coord v)
  let o (v : GridVertex n n) := outDir v (P v)
  let E (v : GridVertex n n) := portAt T n (coord v) (f v) (nb v) (o v)
  let C (v : GridVertex n n) := coverAt T n (coord v) (f v) (nb v)
  let S (a : origins n) := slotAt T n (coord a) (maskAt F a)
  let A (a : origins n) := stripAt T n (coord a) (maskAt F a)
  have ez : (∑ v, ∑ d ∈ range 4, E v d)=0 := by
    apply physical_ports_zero
    · intro v d bad; simp [E,portAt,bond,bad]
    · intro v w d h
      have adj : (gridGraph n n).Adj v w := by
        change adjacent _ _ _ _
        fin_cases d <;> simp [coord,shift,Prod.ext_iff,adjacent,Fin.ext_iff] at h ⊢ <;> omega
      have eq := physical_edge_key F P step covers v w d adj h 0
      have t : turn 0 (d+2)=d+2 := turn0 ⟨_,by have := d.isLt; omega⟩
      have rev : shift (coord w) (d+2)=coord v := by rw [←h]; exact (reverse_step _ d).1
      have l := neighbours_bit F (coord v) (⟨d,by omega⟩ : Fin 4)
      have r := neighbours_bit F (coord w) (⟨d+2,by omega⟩ : Fin 4)
      dsimp only at eq l r
      simp only [h,rev,marked_at] at l r
      simp only [Fin.val_zero] at eq
      rw [out0 ⟨_,outDir_lt v (P v)⟩,out0 ⟨_,outDir_lt w (P w)⟩,turn0 ⟨d,by omega⟩,t] at eq
      simp only [E,portAt,nb,o,f,l,r,eq]; exact bond_flip T d _ h
  have az : (∑ a, ∑ d ∈ range 4, A a d)=0 := by
    apply physical_ports_zero
    · intro p d bad; simp [A,stripAt,bond,bad]
    · intro a b d h
      have eq := physical_overlap_key F (r:=a.1) (c:=a.2) (r':=b.1) (c':=b.2)
        (by have := a.1.isLt; omega) (by have := a.2.isLt; omega)
        (by have := b.1.isLt; omega) (by have := b.2.isLt; omega) d h.symm 0
      have t : turn 0 (d+2)=d+2 := turn0 ⟨_,by omega⟩
      simp only [Fin.val_zero,rot0,turn0 ⟨d,by omega⟩,t] at eq
      change overlapBits (maskAt F a) d=overlapBits (maskAt F b) (d+2) at eq
      simp only [A,stripAt,eq]; exact bond_flip T d _ h
  have cs : (∑ v, ∑ q : Fin 9, C v q)=∑ a, ∑ q : Fin 9, S a q := by
    have H := sum_cover_slots n (extend C) (extend S) (by
      intro p hp q bad
      obtain ⟨v,_,rfl⟩ := mem_image.mp hp
      simp only [extend_coord,C,coverAt,cover,if_neg bad])
      (by
        intro a ha q
        obtain ⟨v,_,rfl⟩ := mem_image.mp ha
        have hr := v.1.isLt; have hc := v.2.isLt
        let x := place v.1 v.2 (by omega : v.1.val+3≤n) (by omega : v.2.val+3≤n)
          (⟨q.val/3,by have := q.isLt; omega⟩,⟨q.val%3,by omega⟩)
        have ex : coord x=coord v+offset q := by ext <;> simp [x,place,offset,coord]
        rw [←ex,extend_coord,extend_coord]
        have eq := physical_incidence_key F v.1 v.2 (by omega) (by omega) q 0
        dsimp only at eq
        simp only [Fin.val_zero,q0,rot0] at eq
        have b0 (p : Pos) : rotBits 0 (neighbours F p)=neighbours F p :=
          bits0 ⟨neighbours F p,code_lt (fun d => marked F (shift p d))⟩
        simp only [b0] at eq
        simp only [C,S,coverAt,slotAt,cover,f,nb,←marked_at F x,ex,add_sub_cancel_right,coord_inside,if_true]
        exact congrArg (slot T n (coord v) q) eq)
    rw [physical_sum,physical_sum] at H
    simpa only [extend_coord,Fin.sum_univ_eq_sum_range] using H
  have st (v : GridVertex n n) : starCost T n (coord v) (f v) (nb v) (o v)-y (coord v)*f v ≤
      pricedMax T n (coord v) (y (coord v)) := by
    let a : Atom := (⟨f v,by dsimp [f]; cases decide (v∈F) <;> decide⟩,
      ⟨nb v,code_lt (fun d => marked F (shift (coord v) d))⟩,⟨o v,outDir_lt v (P v)⟩)
    have hv : starOK n (coord v) (f v) (nb v) (o v) := starOK_physical F acy v _ (fun ne => step _ ne.symm)
    have allow : allowed n (coord v) a := by
      simp only [allowed,a,hv,Bool.true_and,Bool.or_eq_true,bne_iff_ne,beq_iff_eq]
      by_cases h : coord v=(0,0)
      · right; have e : v=root := coord_injective (by simpa [root,coord] using h)
        subst v; simp [o,sink,outDir]
      · exact Or.inl h
    unfold pricedMax
    simpa only [if_pos allow] using (le_sup' (fun a : Atom => if allowed n (coord v) a then
      starCost T n (coord v) a.1 a.2.1 a.2.2-y (coord v)*a.1.val else bottom) (mem_univ a))
  have pt (a : origins n) : patchCost T n (coord a) (maskAt F a) ≤ patchMax T n (coord a) := by
    apply le_sup' (fun m : Fin 512 => patchCost T n (coord a) m)
      (mem_filter.mpr ⟨mem_univ _,physical_mask_ok F acy ..⟩)
  have h := add_le_add (sum_le_sum (s:=univ) (fun v _ => st v)) (sum_le_sum (s:=univ) (fun a _ => pt a))
  change (∑ v, (((T.unit:Int)*f v-(∑ d ∈ range 4, E v d))-(∑ q : Fin 9, C v q)-y (coord v)*f v))+
    (∑ a, ((∑ q : Fin 9, S a q)-(∑ d ∈ range 4, A a d))) ≤ pricedBudget T n y at h
  simp only [sum_sub_distrib,←mul_sum,f,sum_mark,ez,az,cs,sub_zero] at h
  linarith only [h]

theorem budget_sound {n} (hn : 2≤n) (T : Prices) (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic) :
    (T.unit:Int)*F.card ≤ budget T n := by
  simpa [pricedBudget,pricedMax,budget,starMax] using charged_sound hn T F acy (fun _ => 0)

theorem upper {n bound} (hn : 2≤n) (T : Prices) (h : budget T n < (T.unit:Int)*(bound+1:Nat)) :
    maxPreserved n n ≤ bound := by
  obtain ⟨F,m,sc⟩ := (squareMaskScore_iff_le (n:=n) (by omega)).mpr (le_refl (maxPreserved n n))
  have b := budget_sound hn T F (mem_acyclicForcedSets.mp m)
  by_contra! bad
  have s : ((bound+1:Nat):Int) ≤ F.card := by omega
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left s (Int.natCast_nonneg T.unit))) (b.trans_lt h)
end GridGraphs.FiniteOne
