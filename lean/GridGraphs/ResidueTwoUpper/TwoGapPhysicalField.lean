import GridGraphs.ResidueTwoUpper.TwoGapPlaquette

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
open ResidueZero Stencil Words BoundarySix.Connected

def liftAt {n} (f : GridVertex n n → α) (outside : α) (p : Pos) :=
  if h : inside n p then f (onSite p h) else outside
@[simp] theorem lift_coord {n} (f : GridVertex n n → α) (out : α) (v : GridVertex n n) :
    liftAt f out (coord v)=f v := by
  rw [liftAt,dif_pos (coord_inside v)]
  exact congrArg f (coord_injective (coord_onSite ..))

def pull (s : Field) (i j : Int) : Field :=
  ⟨s.mark ∘ shiftAt i j,s.dir ∘ shiftAt i j,s.sheet ∘ shiftAt i j,s.ext ∘ shiftAt i j,s.fs ∘ shiftAt i j⟩
def maskField {n} (F : Finset (GridVertex n n)) : Field := ⟨marked F,fun _ => 4,
  fun _ => false,fun _ _ => false,fun _ _ => false⟩
def actual {n} (F : Finset (GridVertex n n)) (i j : Int) := four (pull (maskField F) i j)

theorem move (i j : Int) (p : Pos) (d : Nat) :
    shiftAt i j (shift p d)=shift (shiftAt i j p) d := by
  unfold shift; split <;> ext <;> simp [shiftAt,site] <;> ring
theorem offsetAt (i j : Int) (p : Pos) (b : Fin 9) :
    shiftAt i j (plus3 p b)=shiftAt i j p+offset b.val := by
  ext <;> simp [plus3,shiftAt,site] <;> ring
theorem base_move (i j : Int) (p : Pos) (v : Bool) :
    shiftAt i j (edgeBase p v)=edgeBase (shiftAt i j p) v := by
  cases v <;> ext <;> simp [edgeBase,shiftAt,site] <;> ring
theorem cell_move (i j : Int) (p : Pos) (d : Nat) :
    shiftAt i j (cellDir p d)=cellDir (shiftAt i j p) d := by
  unfold cellDir; split_ifs <;> ext <;> simp [shiftAt,site] <;> ring

theorem transported {k : Int} (hk : 7≤k) (p : Pos) (f nb o m : Nat) :
    let n := 3*k+2; let a := representative 23 (k-7) p; let b := representative 21 (k-7) p
    twoOrbitStar n p f nb o=twoOrbitStar 23 a f nb o ∧ starOK n p f nb o=starOK 23 a f nb o ∧
    twoOrbitPatch n p m=twoOrbitPatch 23 b m := by
  dsimp only; have E : 3*k+2=23+3*(k-7) := by ring
  have L := starLocation_transport (b:=23) (by decide) (j:=k-7) (by omega) p
  have S (d : Nat) : inside (23+3*(k-7)) (shift p d)=inside 23 (shift (representative 23 (k-7) p) d) := by
    have h := congrArg (fun l : StarLocation => (l.neighbour d).isSome) (L 0)
    simp only [starLocation,image,located] at h
    split_ifs at h <;> simp_all
  rw [E]; simp only [twoOrbitStar,L,starOK,S,twoOrbitPatch,show 23+3*(k-7)-2=21+3*(k-7) by ring,
    patchLocation_transport (b:=21) (by decide) (j:=k-7) (by omega)]; exact ⟨trivial,trivial,rfl⟩

theorem arrow_point {n} {F : Finset (GridVertex n n)} {P : GridVertex n n → GridVertex n n}
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x)) (x y : GridVertex n n) (d : Fin 4)
    (eq : shift (coord x) d=coord y) : outDir x (P x)=d ↔ P x=y := by
  have ne : x≠y := by rintro rfl; fin_cases d <;> simp [shift,coord,Prod.ext_iff] at eq <;> omega
  constructor
  · intro h; by_cases same : P x=x
    · rw [same] at h; simp [outDir] at h; have := d.isLt; omega
    · exact coord_injective ((shift_out (step _ same).1).symm.trans (by rw [h,eq]))
  · intro h; rw [h]; unfold outDir; rw [if_neg ne]
    fin_cases d <;> dsimp [shift,coord] at eq ⊢ <;> simp only [Prod.mk.injEq] at eq <;>
      simp only [Fin.lt_def] <;> split_ifs <;> omega

theorem step_grid {n} {x y : GridVertex n n} (d : Fin 4) (h : shift (coord x) d=coord y) :
    (gridGraph n n).Adj x y := by
  change adjacent _ _ _ _; simp only [adjacent,Fin.ext_iff]
  fin_cases d <;> simp [shift,coord,Prod.ext_iff] at h <;> omega

/-- The global matching and sheet fields use the same orientation as the
exit chart. Neither is an assumption about a SAT witness. -/
structure Global {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (s : Field) : Prop where
  marks : s.mark=marked F
  dirs : s.dir=liftAt (fun x => outDir x (P x)) 4
  turns : ∀ x y z, P x=y → x≠y → P y=z → y≠z →
    s.sheet (coord y)=xor (s.sheet (coord x)) (wrap (outDir x y) (outDir y z))
  owners : OwnerField n s.mark s.ext s.fs

theorem global_of_score {u d} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (C : North.Chart F P d) (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    ∃ s, Global F P s := by
  have cm := corners_marked u F acy score
  have marked : nw u∈F := cm _ (by simp [nw,isCorner])
  have active : ¬isolated F (nw u) := by
    intro no
    have adj : (gridGraph _ _).Adj (nw u) (⟨0,by omega⟩,⟨1,by omega⟩) := Or.inl ⟨rfl,Or.inl rfl⟩
    exact no _ ⟨adj,Or.inl marked⟩
  obtain ⟨ext,fs,owners⟩ := owner_field (by omega) F acy (nw u) active
    (fun _ _ e => (all_active_reachable u F acy score e).1)
  obtain ⟨s,sh⟩ := turn_sheet (by omega) F acy P C.step C.arrows
  exact ⟨⟨ResidueZero.marked F,liftAt (fun x => outDir x (P x)) 4,liftAt s false,ext,fs⟩,rfl,rfl,
    fun _ _ _ xy ne yz ny => by simp only [lift_coord]; exact sh _ _ _ xy ne yz ny,owners⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
