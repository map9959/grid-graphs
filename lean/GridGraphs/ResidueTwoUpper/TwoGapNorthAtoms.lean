import GridGraphs.ResidueTwoUpper.TwoGapNorthRun

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
open ResidueZero Stencil

private theorem rep_fold (u j : Nat) (t b : Int) (hb : b=23 ∨ b=21) (ht : -1≤t ∧ t≤1)
    (hj : j≤35+42*u) :
    rep b (4+14*(u:Int)) (j+t)=rep b 4 ((tag u j:Int)+t) := by
  unfold rep tag; split_ifs <;> omega

private theorem star_transport (u j r : Nat) (hj : j<35+42*u) (hr : r<5) (f nb o : Nat) :
    twoOrbitStar (35+42*(u:Int)) (r,j) f nb o=twoOrbitStar 35 (r,tag u j) f nb o := by
  let a : Int := 4+14*u
  have E : 35+42*(u:Int)=23+3*a := by dsimp [a]; ring
  have W (s : Int) (hs : 0 ≤ s) (p : Pos) :
      twoOrbitStar (23+3*s) p f nb o=twoOrbitStar 23 (representative 23 s p) f nb o := by
    simp only [twoOrbitStar,starLocation_transport (b:=23) (by decide) (j:=s) hs]
  rw [E,W a (by dsimp [a]; positivity),show (35:Int)=23+3*4 by decide,W 4 (by decide)]
  congr 1; apply Prod.ext
  · dsimp [representative,rep]; split_ifs <;> omega
  · simpa only [add_zero,a,representative] using rep_fold u j 0 23 (by decide) (by decide) (by omega)

theorem patch_transport (u j r : Nat) (hj : j<35+42*u) (hr : r<4) (m : Nat) :
    twoOrbitPatch (35+42*(u:Int)) (r,(j:Int)-1) m=twoOrbitPatch 35 (r,(tag u j:Int)-1) m := by
  let a : Int := 4+14*u
  have W (s : Int) (hs : 0 ≤ s) (p : Pos) :
      twoOrbitPatch (23+3*s) p m=twoOrbitPatch 23 (representative 21 s p) m := by
    simp only [twoOrbitPatch,show 23+3*s-2=21+3*s by ring,patchLocation_transport (b:=21) (by decide) hs]; rfl
  rw [show 35+42*(u:Int)=23+3*a by dsimp [a]; ring,W a (by dsimp [a]; positivity),
    show (35:Int)=23+3*4 by decide,W 4 (by decide)]
  congr 1; apply Prod.ext
  · dsimp [representative,rep]; split_ifs <;> omega
  · simpa only [sub_eq_add_neg,a,representative] using rep_fold u j (-1) 21 (by decide) (by decide) (by omega)

theorem star_entry {u d j r : Nat} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (C : Chart F P d) (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (wrong : d%3≠2) (x : GridVertex (35+42*u) (35+42*u)) (pos : rc x=(r,j)) (hr : r<5) :
    cornerStar (tag u j) r (decide (x∈F)).toNat (neighbours F (coord x)) (outDir x (P x)) := by
  obtain ⟨v,ex,price,zero⟩ := C.sole
  have X := x.1.isLt; have J := x.2.isLt
  obtain ⟨R,K⟩ := Prod.mk.inj pos
  have co : coord x=((r:Int),(j:Int)) := by simp [coord,R,K]
  have bound : j<35+42*u := K ▸ J
  have o := starOK_physical F acy x (P x) (fun h => C.step _ h.symm)
  have left : (tag u j=0 ↔ j=0) := by unfold tag; split_ifs <;> omega
  have insideEq (i : Nat) : inside (35+42*(u:Int)) (shift ((r:Int),j) i)=
      inside 35 (shift ((r:Int),tag u j) i) := by
    have ax (t : Int) (ht : -1≤t ∧ t≤1) : (0≤(j:Int)+t ∧ (j:Int)+t<35+42*(u:Int)) ↔
        (0≤(tag u j:Int)+t ∧ (tag u j:Int)+t<35) := by unfold tag; split_ifs <;> omega
    unfold shift; split <;> apply Bool.eq_iff_iff.mpr <;> simp only [inside,Bool.and_eq_true,decide_eq_true_eq]
    all_goals have A := ax (-1) (by decide); have B := ax 0 (by decide); have D := ax 1 (by decide); omega
  change starOK (35+42*(u:Int)) (coord x) _ _ _=true at o
  rw [co] at o
  have ok : starOK 35 (r,tag u j) (decide (x∈F)).toNat (neighbours F (coord x)) (outDir x (P x)) := by
    -- Transport only the position, not the neighbor bits.
    rw [co]; simpa only [starOK,insideEq] using o
  have root : P (nw u)=nw u := by
    apply rc_inj; exact C.perimeter (nw u) (Or.inl rfl)
  have normal : x≠nw u → P x=x → x∉F ∧ neighbours F (coord x)=0 := by
    intro ne fix
    have isolated {y} (edge : (Bonds F).Adj x y) : False := ne
      (Frame.isolated_fixed P C.arrows root (all_active_reachable u F acy score edge).1 fix).symm
    have no : x∉F := by
      intro m
      let y : GridVertex (35+42*u) (35+42*u) := (⟨r+1,by omega⟩,x.2)
      have e : (gridGraph _ _).Adj x y := Or.inr ⟨rfl,Or.inl (by dsimp [y]; omega)⟩
      exact isolated ⟨e,Or.inl m⟩
    refine ⟨no,?_⟩
    have bits (i : Fin 4) : bit (neighbours F (coord x)) i=0 := by
      rw [neighbours_bit]; by_cases m : marked F (shift (coord x) i)
      · obtain ⟨y,mem,eq⟩ := Finset.mem_image.mp (show shift (coord x) i∈F.image coord by simpa [marked] using m)
        have e : (gridGraph _ _).Adj x y := by
          change adjacent _ _ _ _; simp only [adjacent,Fin.ext_iff]
          fin_cases i <;> simp [shift,coord,Prod.ext_iff] at eq <;> omega
        exact (isolated ⟨e,Or.inr mem⟩).elim
      · simp [Bool.eq_false_iff.mpr m]
    exact (by native_decide : ∀ z : Fin 16, (∀ i : Fin 4, bit z i=0) → z.val=0) ⟨neighbours F (coord x),code_lt _⟩ bits
  unfold cornerStar; dsimp only
  simp only [Bool.and_eq_true,ok,true_and,Bool.or_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq]
  constructor
  · split_ifs with isRoot
    · have eq : x=nw u := rc_inj (pos.trans (Prod.ext isRoot.2 (left.mp isRoot.1)))
      simp [eq,root,outDir]
    · by_cases fixed : P x=x
      · have ne : x≠nw u := by rintro rfl; dsimp [nw,rc] at pos; simp only [Prod.mk.injEq] at pos; apply isRoot; exact ⟨left.mpr pos.2.symm,pos.1.symm⟩
        obtain ⟨no,b⟩ := normal ne fixed; simp [no,b]
      · simp only [Bool.or_eq_true]; left; apply bne_iff_ne.mpr; unfold outDir; rw [if_neg (Ne.symm fixed)]; split_ifs <;> decide
  · have trans := star_transport u j r bound hr (decide (x∈F)).toNat (neighbours F (coord x)) (outDir x (P x))
    rw [←trans,←co]
    by_cases e : x=v
    · subst v
      right
      have bd : IsGridBoundary x := Or.inl (congrArg Prod.fst ex)
      have out := C.perimeter _ bd
      rw [ex] at out
      have H := C.ordinary
      have out' : rc (P x)=(1,d) := by simpa [parent,show d≠0 by omega,show d≠1 by omega] using out
      have eqp := pos.symm.trans ex
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eqp
      have dir : outDir x (P x)=1 := by
        have nr := congrArg Prod.fst ex; have nc := congrArg Prod.snd ex
        have yr := congrArg Prod.fst out'; have yc := congrArg Prod.snd out'
        dsimp [rc] at nr nc yr yc
        have ne : x≠P x := fun e => by have h := congrArg (fun z : GridVertex (35+42*u) (35+42*u) => z.1.val) e; omega
        unfold outDir; rw [if_neg ne]; simp only [Fin.lt_def]; split_ifs <;> omega
      change twoOrbitStar (35+42*(u:Int)) (coord x) _ _ _=full at price
      rw [price,dir]; simp only [true_and,decide_eq_true_eq,beq_self_eq_true,bne_iff_ne]
      unfold tag; split_ifs <;> omega
    · left; exact zero (.inl x) (fun h => e (Sum.inl.inj h))

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North.Scan
