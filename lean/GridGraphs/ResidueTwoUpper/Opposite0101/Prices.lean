import GridGraphs.ResidueTwoUpper.Opposite0101.StencilReplay

namespace GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
open ResidueZero Stencil BoundarySix.Connected

private theorem repFold {u r j : Nat} (hr : r<7) (d : Nat) (hd : d=0 ∨ d=2) :
    representative (35-d:ℤ) (14*u) (xy false (r:Int) (j:Int)) =
      representative (35-d:ℤ) 0 (xy false (r:Int) ((idx u j:Int))) := by
  rcases hd with rfl|rfl <;> ext <;> dsimp [representative,rep,xy,idx] <;> split_ifs <;> omega

private theorem fold {u r j : Nat} (v : Bool) (hr : r<7) (d : Nat) (hd : d=0 ∨ d=2) :
    representative (35-d:ℤ) (14*u) (xy v (r:Int) (j:Int)) =
      representative (35-d:ℤ) 0 (xy v (r:Int) ((idx u j:Int))) := by
  cases v
  · exact repFold hr d hd
  · have eq := congrArg Prod.swap (repFold (u:=u) (j:=j) hr d hd)
    exact eq

theorem starCost_fold {u r j : Nat} (v : Bool) (hr : r<7) (f nb o : Nat) :
    twoOrbitStar (35+42*(u:Int)) (xy v r j) f nb o =
      twoOrbitStar 35 (xy v r (idx u j)) f nb o := by
  let pos (J : Nat) := xy v (r:Int) (J:Int)
  have T (x : Nat) (J : Nat) : twoOrbitStar (35+42*(x:Int)) (pos J) f nb o =
      twoOrbitStar 35 (representative 35 (14*x) (pos J)) f nb o := by
    have en : 35+42*(x:Int)=35+3*(14*(x:Int)) := by ring
    simp only [twoOrbitStar,en,starLocation_transport (b:=35) (by decide) (j:=14*(x:Int)) (by positivity)]
  exact (T u j).trans ((congrArg (fun p => twoOrbitStar 35 p f nb o) (fold v hr 0 (Or.inl rfl))).trans
    (by simpa [pos] using (T 0 (idx u j)).symm))

theorem patchCost_fold {u r j : Nat} (v : Bool) (hr : r<7) (m : Nat) :
    twoOrbitPatch (35+42*(u:Int)) (xy v r j) m = twoOrbitPatch 35 (xy v r (idx u j)) m := by
  let pos (J : Nat) := xy v (r:Int) (J:Int)
  have T (x : Nat) (J : Nat) : twoOrbitPatch (35+42*(x:Int)) (pos J) m =
      twoOrbitPatch 35 (representative 33 (14*x) (pos J)) m := by
    have en : 35+42*(x:Int)-2=33+3*(14*(x:Int)) := by ring
    simp only [twoOrbitPatch,en,patchLocation_transport (b:=33) (by decide) (j:=14*(x:Int)) (by positivity)]
    rfl
  exact (T u j).trans ((congrArg (fun p => twoOrbitPatch 35 p m) (fold v hr 2 (Or.inr rfl))).trans
    (by simpa [pos] using (T 0 (idx u j)).symm))

private theorem starOK_fold {u r j : Nat} (v : Bool) (hr : r<6) (hj : j<35+42*u) (f nb o : Nat) :
    starOK (35+42*(u:Int)) (xy v r j) f nb o = starOK 35 (xy v r (idx u j)) f nb o := by
  have h (d : Nat) : inside (35+42*(u:Int)) (shift (xy v r j) d) =
      inside 35 (shift (xy v r (idx u j)) d) := by
    cases v <;> unfold xy shift inside <;> split <;> dsimp [idx] <;> split_ifs <;>
      apply Bool.eq_iff_iff.mpr <;> simp <;> omega
  simp only [starOK,h]

structure Prices (n : Nat) (F : Finset (GridVertex n n)) : Prop where
  star : ∀ x, ∃ o : Fin 5,
    starOK n (coord x) (decide (x∈F)).toNat (neighbours F (coord x)) o ∧
    (twoOrbitStar n (coord x) (decide (x∈F)).toNat (neighbours F (coord x)) o=0 ∨
     IsGridBoundary x ∧ twoOrbitStar n (coord x) (decide (x∈F)).toNat (neighbours F (coord x)) o=full)
  patch : ∀ a : origins n, maskOK (maskAt F a) ∧ twoOrbitPatch n (coord a) (maskAt F a)=0
  corners : ∀ x, isCorner x → x∈F

theorem prices_of_score {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) : Prices _ F := by
  obtain ⟨P,d,step,_,paid,zero,_,cases'⟩ := Frame.frame_of_score u F acy score
  obtain ⟨_,v,_,rfl⟩ := cases'.resolve_left (by omega)
  refine ⟨fun x => ⟨⟨outDir x (P x),outDir_lt ..⟩,
    starOK_physical F acy x (P x) (fun h => step x h.symm),?_⟩,?_,
    corners_marked u F acy score⟩
  · by_cases e : x=v.1
    · subst x; exact Or.inr ⟨v.2,paid⟩
    · exact Or.inl (zero (.inl x) (fun eq => e (Sum.inl.inj eq)))
  · intro a; exact ⟨physical_mask_ok F acy a.1 a.2 (by have := a.1.isLt; omega)
      (by have := a.2.isLt; omega),zero (.inr a) (fun eq => by cases eq)⟩

theorem star_entry_physical {u} {F : Finset (GridVertex (35+42*u) (35+42*u))}
    (prices : Prices _ F) (v : Bool) (r j : Nat) (hr : r<6) (hj : j<35+42*u) :
    let x := vertex v r j (by omega) hj
    (sTab v (idx u j) r).testBit ((decide (x∈F)).toNat + 2*neighbours F (coord x))=true := by
  let n := 35+42*u
  let x := vertex v r j (by omega) hj
  have coordX : coord x=xy v (r:Int) (j:Int) := by cases v <;> rfl
  obtain ⟨o,ok,cost⟩ := prices.star x
  let f : Fin 2 := ⟨(decide (x∈F)).toNat,by cases decide (x∈F) <;> decide⟩
  let nb : Fin 16 := ⟨neighbours F (coord x),code_lt _⟩
  have i := (idx_pair hj).1
  have E : idx u j=0 ↔ j=0 := by unfold idx; split_ifs <;> omega
  have Z : idx u j=34 ↔ j+1=n := by dsimp [n]; unfold idx; split_ifs <;> omega
  apply starReplay v ⟨idx u j,i⟩ ⟨r,hr⟩ f nb o
  · change starOK (35+42*(u:Int)) (coord x) f nb o=true at ok
    rwa [coordX,starOK_fold v hr hj] at ok
  · intro h
    have isc : isCorner x := by
      cases v <;> dsimp [Frame.ends,xy,isCorner,x,vertex] at h ⊢ <;> dsimp [n] at * <;> omega
    simp [f,prices.corners x isc]
  · change twoOrbitStar (35+42*(u:Int)) (coord x) f nb o=0 ∨
      IsGridBoundary x ∧ twoOrbitStar (35+42*(u:Int)) (coord x) f nb o=full at cost
    rw [coordX,starCost_fold v (by omega)] at cost
    rcases cost with z|⟨bd,z⟩
    · exact Or.inl z
    · refine Or.inr ⟨?_,z⟩
      cases v <;> dsimp [x,vertex,xy,IsGridBoundary] at bd <;> dsimp [n] at * <;> omega

theorem patch_entry_physical {u} {F : Finset (GridVertex (35+42*u) (35+42*u))}
    (prices : Prices _ F) (v : Bool) (r j : Nat) (hr : r<5) (hj : j+2<35+42*u) :
    let a : origins (35+42*u) := xy v ⟨r,by omega⟩ ⟨j,by omega⟩
    (pTab v (idx u j) r).testBit (maskAt F a)=true := by
  let a : origins (35+42*u) := xy v ⟨r,by omega⟩ ⟨j,by omega⟩
  have A : coord a=xy v (r:Int) (j:Int) := by cases v <;> rfl
  have q := prices.patch a
  apply patchReplay v ⟨idx u j,by unfold idx; split_ifs <;> omega⟩ ⟨r,hr⟩ (maskAt F a) q.1
  have z := q.2
  change twoOrbitPatch (35+42*(u:Int)) (coord a) (maskAt F a)=0 at z
  rwa [A,patchCost_fold v (by omega)] at z

end GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
