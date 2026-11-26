import GridGraphs.ResidueTwoUpper.ExceptionalFramePropagation

namespace GridGraphs.ResidueTwoUpper.Exceptional.Frame
open ResidueZero Stencil Finset

def depthAt (n : Nat) (p : Pos) := min (depth (n-1) p.1) (depth (n-1) p.2)
def straight (n : Nat) (p : Pos) := depthAt n p=0 ∧ 3 ≤ max (depth (n-1) p.1) (depth (n-1) p.2)

private theorem near {n : Nat} (hn : 23≤n) (d : Int) (hd : d=5 ∨ d=6)
    (x : Int) (hx : 0≤x ∧ x<n) (k : Int) (hk : 0≤k ∧ k<3) :
    (depth (2*d+2) (axis n d x)=k ↔ depth (n-1) x=k) ∧
    (k<depth (2*d+2) (axis n d x) ↔ k<depth (n-1) x) := by
  unfold depth axis; split_ifs <;> omega

private theorem tag_end {n : Nat} (hn : 23≤n) (d : Int) (hd : d=5 ∨ d=6)
    (x : Int) (hx : 0≤x ∧ x<n) :
    (axis n d x=0 ↔ x=0) ∧ (axis n d x=2*d+2 ↔ x=(n:Int)-1) := by
  unfold axis; split_ifs <;> omega

def allGood {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n) :
    occurrence n → Bool := Sum.elim (fun v => S n (coord v) (decide (v∈F)).toNat
      (neighbours F (coord v)) (outDir v (P v))) (fun a => W n (coord a) (maskAt F a))

theorem frame_checked (cs : baseS) (cp : baseP) (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (acy : (Bonds F).IsAcyclic) (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (corners : ∀ x, isCorner x → x∈F) (w : ∀ x, weightAt F P x=0 ∨ weightAt F P x=full) :
    ∀ x, allGood F P x := by
  let n := 35+42*u; let j := 4+14*u
  have e : (n:Int)=23+3*(j:Int) := by dsimp [n,j]; omega
  have ep : ((n-2:Nat):Int)=21+3*(j:Int) := by dsimp [n,j]; omega
  apply eliminate (n:=n) (by dsimp [n]; omega)
  intro x
  cases x with
  | inl v =>
    let f : Fin 2 := ⟨(decide (v∈F)).toNat,by cases decide (v∈F) <;> decide⟩
    let nb : Fin 16 := ⟨neighbours F (coord v),code_lt _⟩
    let o : Fin 5 := ⟨outDir v (P v),outDir_lt ..⟩
    have ok := starOK_physical F acy v _ (fun h => step _ h.symm)
    have c : ends 14 (axis n 6 (coord v).1) (axis n 6 (coord v).2) → f.val=1 := by
      intro ec; obtain ⟨a,b⟩ := ec
      have lim (i : Fin n) := tag_end (n:=n) (by dsimp [n]; omega) 6 (Or.inr rfl) i.val
        (by have := i.isLt; omega)
      have A := lim v.1; have B := lim v.2; norm_num only at A B
      have ic : isCorner v := by unfold isCorner; dsimp only [coord] at a b; dsimp only [n] at A B a b; omega
      simp [f,corners v ic]
    have wx := w (Sum.inl v)
    change twoOrbitStar n (coord v) f nb o=0 ∨ twoOrbitStar n (coord v) f nb o=full at wx
    change traceOK (starRank n (coord v) f nb false) (starRank n (coord v) f nb true) (S n (coord v) f nb o)
    rw [e] at c wx ⊢
    exact traces_star cs j (e ▸ coord_inside v) f nb o (e ▸ ok) c wx
  | inr a =>
    have ok := physical_mask_ok F acy a.1 a.2 (by have := a.1.isLt; omega) (by have := a.2.isLt; omega)
    have wx := w (Sum.inr a)
    change twoOrbitPatch n (coord a) (maskAt F a)=0 ∨ twoOrbitPatch n (coord a) (maskAt F a)=full at wx
    change traceOK (patchRank n (coord a) _ true) (patchRank n (coord a) _ false) (W n (coord a) _)
    rw [e] at wx ⊢
    exact traces_patch cp j (ep ▸ coord_inside a) _ ok wx

def inward {n} (P : GridVertex n n → GridVertex n n) (v : GridVertex n n) :=
  depthAt n (coord v)=0 ∧ depthAt n (coord (P v))=1

private theorem inward_geom {n} (hn : 35≤n) (v w : GridVertex n n)
    (e : (gridGraph n n).Adj v w) (d : depthAt n (coord v)=0) :
    (¬ends ((n:Int)-1) v.1.val v.2.val ∧
      ((v.1.val:Int)=0 ∧ outDir v w=1 ∨ (v.1.val:Int)=n-1 ∧ outDir v w=3 ∨
       (v.2.val:Int)=0 ∧ outDir v w=0 ∨ (v.2.val:Int)=n-1 ∧ outDir v w=2)) ↔
      depthAt n (coord w)=1 := by
  have a := v.1.isLt; have b := v.2.isLt; have c := w.1.isLt; have f := w.2.isLt
  have ne := e.ne
  change adjacent n n v w at e
  simp only [adjacent,Fin.ext_iff] at e
  simp only [depthAt,coord,depth,ends,outDir,Fin.lt_def,if_neg ne] at *
  have ends0 (x y : Int) (a : 0≤x) (b : x<n) (c : 0≤y) (f : y<n) :
      min (min x (n-1-x)) (min y (n-1-y))=0 ↔ x=0 ∨ x=n-1 ∨ y=0 ∨ y=n-1 := by omega
  have ends1 (x y : Int) : min (min x (n-1-x)) (min y (n-1-y))=1 ↔
      (1≤x ∧ x≤n-2 ∧ 1≤y ∧ y≤n-2) ∧ (x=1 ∨ x=n-2 ∨ y=1 ∨ y=n-2) := by omega
  rw [ends0 _ _ (by omega) (by omega) (by omega) (by omega)] at d
  rw [ends1]
  rcases e with ⟨x,y|y⟩|⟨x,y|y⟩ <;> split_ifs <;> norm_num <;> omega

theorem star_geometry {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x)) (v : GridVertex n n) (h : allGood F P (Sum.inl v)) :
    (straight n (coord v) → v∈F) ∧ (depthAt n (coord v)=1 → v∉F) ∧
    (depthAt n (coord v)=0 → (starSlack F P v=full ↔ inward P v)) ∧
    (depthAt n (coord v)≠0 ∧ starSlack F P v=full →
      depthAt n (coord v)=2 ∧ v∉F ∧ neighbours F (coord v)=0 ∧ P v=v) := by
  change starGood _ _ _ _ _ _=true at h
  simp only [starGood,decide_eq_true_eq] at h
  obtain ⟨hm,hb,hw,hi⟩ := h
  let a := (coord v).1; let b := (coord v).2
  have loc (i : Fin n) (k : Int) (hk : 0≤k ∧ k<3) := near (n:=n) (by omega) 6 (Or.inr rfl)
    i.val (by have := i.isLt; omega) k hk
  have dif (i : Fin n) := tag_end (n:=n) (by omega) 6 (Or.inr rfl) i.val (by have := i.isLt; omega)
  have r0 := loc v.1 0 (by decide); have c0 := loc v.2 0 (by decide)
  have r1 := loc v.1 1 (by decide); have c1 := loc v.2 1 (by decide)
  have r2 := loc v.1 2 (by decide); have c2 := loc v.2 2 (by decide)
  have ra := dif v.1; have ca := dif v.2
  norm_num only at r0 c0 r1 c1 r2 c2 ra ca
  simp only [coord] at hm hb hw hi
  have trans (k : Int) (hk : 0≤k ∧ k<3) :
      min (depth 14 (axis n 6 v.1.val)) (depth 14 (axis n 6 v.2.val))=k ↔ depthAt n (coord v)=k := by
    have A := loc v.1 k hk; have B := loc v.2 k hk
    norm_num only at A B
    unfold depthAt; dsimp [coord]; omega
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨d,far⟩; have A := (trans 0 (by decide)).mpr d
    simp only [coord] at far
    have one := hm ⟨A,by omega⟩
    by_contra no; simp [no] at one
  · intro d mem
    have zero := hb ((trans 1 (by decide)).mpr d)
    simp [mem] at zero
  · intro d; rw [show starSlack F P v=full ↔ _ from hw ((trans 0 (by decide)).mpr d)]
    by_cases fixed : P v=v
    · simp [fixed,outDir,inward,d]
    · have adj := (step v fixed).1
      simp only [inward,d,true_and]
      have geom := inward_geom hn v (P v) adj d
      simp only [ends,ra.1,ra.2,ca.1,ca.2]; exact geom
  · rintro ⟨d,w⟩
    obtain ⟨dd,ff,bb,oo⟩ := hi ⟨fun h => d ((trans 0 (by decide)).mp h),w⟩
    refine ⟨(trans 2 (by decide)).mp dd,?_,bb,?_⟩
    · intro mem; simp [mem] at ff
    · by_contra no
      have nd : outDir v (P v)<4 := by
        unfold outDir; rw [if_neg (Ne.symm no)]; split_ifs <;> decide
      omega

theorem patch_geometry {n} (hn : 35≤n) (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (a : origins n) (h : allGood F P (Sum.inr a)) :
    (patchSlack F a=full → 0<depthAt (n-2) (coord a)) ∧
    (isCorner a → word (coord a).1 (coord a).2 (maskAt F a) ∈ [3,7,12,13]) := by
  change patchGood _ _ _ _=true at h
  simp only [patchGood,decide_eq_true_eq] at h
  have cast : (n:Int)-2=((n-2:Nat):Int) := by omega
  rw [cast] at h
  have A (i : Fin (n-2)) := tag_end (n:=n-2) (by omega) 5 (Or.inl rfl) i.val (by have := i.isLt; omega)
  have B (i : Fin (n-2)) := near (n:=n-2) (by omega) 5 (Or.inl rfl) i.val
    (by have := i.isLt; omega) 0 (by decide)
  have ar := A a.1; have ac := A a.2; have br := B a.1; have bc := B a.2
  norm_num only at ar ac br bc
  obtain ⟨hw,hc⟩ := h
  simp only [coord] at hw hc ⊢
  constructor
  · intro w; have := hw w; unfold depthAt; dsimp [coord]; omega
  · intro corner
    have en : ends 12 (axis (n-2:Nat) 5 a.1.val) (axis (n-2:Nat) 5 a.2.val) := by
      unfold isCorner at corner; unfold ends; omega
    have use := hc en
    simpa only [word,ar.1,ac.1] using use

end GridGraphs.ResidueTwoUpper.Exceptional.Frame
