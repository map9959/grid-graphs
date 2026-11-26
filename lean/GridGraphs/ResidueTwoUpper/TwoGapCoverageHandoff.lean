import GridGraphs.ResidueTwoUpper.TwoGapCoverageCommon

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
open Catalogue ExitReplay ResidueZero Stencil Words BoundarySix.Connected

def BaseCover : Prop := ∀ c ∈ allKeys, ∀ l, Local c.stamp l → band (four l) ∈ catalogue (bucket c)

private theorem key_mem {k q : Nat} (hk : k=11 ∨ k=25) (lo : 1≤q) (hi : q+2≤k)
    {c} (h : c∈casesFor k q) : c∈allKeys := by
  apply List.mem_flatMap.mpr; refine ⟨k,by simp [hk],?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨q-1,List.mem_range.mpr (by omega),?_⟩
  simpa [show q-1+1=q by omega] using h

private theorem middle_exit (cover : BaseCover) {k q : Nat} (hk : k=11 ∨ k=25) (lo : 1≤q) (hi : q+2≤k)
    (s : Field) (x : Int)
    (L : Local (sig k q ((q:Int)-1) 0) (pull s (x-1) 0))
    (R : Local (sig k q q 0) (pull s x 0)) : 3≤q ∧ q+4≤k := by
  have cast : ((q-1:Nat):Int)=(q:Int)-1 := by omega
  by_contra bad
  by_cases near : q<3
  · let c := ChartKey.mk k q (q-1) 0
    have hc : c∈casesFor k q := by simp [casesFor,near,c]
    have H := cover c (key_mem hk lo hi hc) _ (by simpa [c,ChartKey.stamp,cast] using L)
    simpa [c,bucket,catalogue,near] using H
  · have far : k-4<q := by omega
    let c := ChartKey.mk k q q 0
    have hc : c∈casesFor k q := by simp [casesFor,near,far,c]
    have H := cover c (key_mem hk lo hi hc) _ R
    simp [c,bucket,catalogue,near,far] at H; omega

private theorem inside_rows (cover : BaseCover) {k q j : Nat} (hk : k=11 ∨ k=25)
    (lo : 3≤q) (hi : q+4≤k) (hj : j+1<k) (l r : Field)
    (L : Local (sig k q ((q:Int)-1) j) l) (R : Local (sig k q q j) r) :
    band (four l) ∈ tables[level k j]! ∧ band (four r) ∈ tables[level k j]! := by
  have near : ¬q<3 := by omega
  have far : ¬k-4<q := by omega
  let c := ChartKey.mk k q (q-1) j
  let d := ChartKey.mk k q q j
  have mem (x) (hx : x∈[c,d]) : x∈allKeys := by
    apply key_mem hk (by omega : 1≤q) (by omega)
    simp only [casesFor,if_neg near,if_neg far,List.mem_flatMap]
    exact ⟨j,List.mem_range.mpr (by omega),hx⟩
  have w : level k j<5 := by unfold level; split_ifs <;> omega
  have left := cover c (mem _ (by simp)) _ (by simpa [ChartKey.stamp,c,show ((q-1:Nat):Int)=(q:Int)-1 by omega] using L)
  have right := cover d (mem _ (by simp)) _ R
  have lt₀ : 2*level k j<10 := by omega
  have lt₁ : 2*level k j+1<10 := by omega
  simpa [c,d,bucket,catalogue,near,far,show (q-1==q)=false by simp; omega,lt₀,lt₁,Nat.mul_add_div] using And.intro left right

/-- Row selection is in physical coordinates; a repeated middle row
has the same table on both sides of the collapsed bond. -/
theorem physical_of_baseCover (cover : BaseCover) {u}
    (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (canon : packed (signature (by omega) F)=code4 0 0 1 1) :
    ∃ P q s, North.Chart F P (2+3*q) ∧ Global F P s ∧
      (∀ i j : Int, four (pull s i j)=actual F i j) ∧
      3≤q ∧ q+4≤11+14*u ∧ ∀ j : Nat, j+1<11+14*u →
      permits tables[level (11+14*u) j]! (stripWord s q j) (stripWord s q ((j:Int)+1)) := by
  obtain ⟨P,q,s,C,G,M,H⟩ := physical_to_folded F acy score two canon
  refine ⟨P,q,s,C,G,M,?_⟩
  rcases H with ⟨rfl,lo,hi,L⟩|⟨p,a,b,lo,hi,rfl,sz,left,right,L⟩
  · obtain ⟨west,east⟩ := middle_exit cover (Or.inl rfl) lo (by omega : q+2≤11) s q (L _ _) (L _ _)
    refine ⟨west,east,?_⟩
    intro j hj; apply (permits_iff ..).mpr
    exact inside_rows cover (Or.inl rfl) west east hj _ _ (L _ _) (L _ _)
  · have col := exit_columns (Int.natCast_nonneg a) (Int.natCast_nonneg b) (p:=(p:Int)) (by exact_mod_cast left) (by exact_mod_cast right)
    have lhs (j : Int) := L (((p:Int)+a)-1) j
    have rhs (j : Int) := L ((p:Int)+a) j
    simp only [col.1,col.2] at lhs rhs
    have z : row a b 0=0 := by simp [row,fold]
    obtain ⟨west,east⟩ := middle_exit cover (Or.inr rfl) lo (by omega : p+2≤25) s ((p:Int)+a)
      (by simpa only [z,Nat.cast_ofNat] using lhs 0) (by simpa only [z,Nat.cast_ofNat] using rhs 0)
    refine ⟨by omega,by omega,?_⟩
    intro j hj; apply (permits_iff ..).mpr
    let y := row a b j
    have bounds : 0≤y ∧ y+1<25 := by unfold y row fold; split_ifs <;> omega
    have yr : (y.toNat:Int)=y := Int.toNat_of_nonneg bounds.1
    have tag : level (11+14*u) j=level 25 y.toNat := by unfold level y row fold at *; split_ifs <;> omega
    rw [tag,Nat.cast_add]
    apply inside_rows cover (Or.inr rfl) west east (by omega)
    · simpa only [yr,y,Nat.cast_ofNat] using lhs j
    · simpa only [yr,y,Nat.cast_ofNat] using rhs j

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
