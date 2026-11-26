import GridGraphs.NoPitch.Budget.ExactPaths
import GridGraphs.NoPitch.StarCoverage
import GridGraphs.NoPitch.Certificate

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset GridGraphs.NoPitch.Dual Keys
attribute [local irreducible] chart19 chart58 chart61
variable {k : Nat}

private theorem scatter_pos {A : Type} [Fintype A] (D : Chart) (f : A → Nat) (j) :
    0 ≤ scatter D (index D) f j := sum_nonneg fun _ _ => by split <;> positivity

theorem physical_nonneg (D : Chart) (F : Finset (Site k)) (o : Site k → Option (Fin 4))
    (j : Fin D.cols.size) : 0≤physicalVector D F o j := by
  have pos {A : Type} [Fintype A] (f : A → Nat) := scatter_pos D f j
  unfold physicalVector counts
  apply add_nonneg (add_nonneg (add_nonneg (add_nonneg (pos _) (pos _)) (pos _)) (pos _))
  split
  · exact le_max_left .. 
  · rfl

def codeBit (mask d : Nat) := mask.testBit d
def keyCorner (n mask : Nat) (f : Bool) :=
  8*starCode n 0 0 (fun d => if d=0 ∨ d=1 then (codeBit mask d).toNat else 9) none+f.toNat

def checkCorner (D : Chart) (n : Nat) := Id.run do
  if h : 0<D.rows.size then
    let i : Fin D.rows.size := ⟨0,h⟩
    let m := index D
    return D.rows[i].sense==2 && D.rows[i].rhs==⟨2,0,0⟩ &&
      D.cols.all (fun c => decide (0≤coeff 0 c.terms)) &&
      (List.range 3).all (fun mask => [false,true].all fun f =>
        (locate D m (keyCorner n mask f)).any fun j => coeff 0 D.cols[j].terms*D.cols[j].units==8)
  else return false

private theorem checked19 : checkCorner chart19 19 := by native_decide
private theorem checked58 : checkCorner chart58 58 := by native_decide
private theorem checked61 : checkCorner chart61 61 := by native_decide

private theorem corner_lookup {D : Chart} {n : Nat} (ok : checkCorner D n) (mask : Nat) (hm : mask<3)
    (f : Bool) : ∃ j, locate D (index D) (keyCorner n mask f)=some j ∧
      coeff 0 D.cols[j].terms*D.cols[j].units=8 := by
  unfold checkCorner at ok
  split at ok
  · simp only [Id.run_pure,Bool.and_eq_true,List.all_eq_true,List.mem_range] at ok
    have h := ok.2 mask hm f (by cases f <;> simp)
    cases e : locate D (index D) (keyCorner n mask f) <;> simp_all
  · contradiction

private theorem corner_key (F : Finset (Site k)) (hk : 0<k) (acy : (G F).IsAcyclic) :
    ∃ mask<3, star F (out F) (origin k)=keyCorner (N k) mask (decide (origin k∈F)) := by
  have zero := (out_none F _).mpr (parent_origin F)
  let one : Fin (N k) := ⟨1,by unfold N; omega⟩
  let a : Site k := (0,one)
  let b : Site k := (one,0)
  have no : ¬(a∈F ∧ b∈F) := fun h => CarrierLayers.ThreeCarrier.diagonal_preserved_false
    _ acy a b h.1 h.2 (.inl rfl) (.inr rfl)
  have bits (d : Nat) (hd : d<4) : neighbor F (origin k) d =
      if d=0 then (decide (a∈F)).toNat else if d=1 then (decide (b∈F)).toNat else 9 := by
    have o : origin k=(0,0) := rfl
    interval_cases d <;> simp [neighbor,probe,o,N,one,a,b,show 0<3*k by omega]
  obtain ⟨mask,hm,eq⟩ : ∃ mask<3, ∀ d<4, neighbor F (origin k) d=
      if d=0 ∨ d=1 then (codeBit mask d).toNat else 9 := by
    by_cases ha : a∈F <;> by_cases hb : b∈F
    · exact False.elim (no ⟨ha,hb⟩)
    · refine ⟨1,by decide,?_⟩
      intro d hd; rw [bits d hd]; interval_cases d <;> simp [ha,hb,codeBit]; decide
    · refine ⟨2,by decide,?_⟩
      intro d hd; rw [bits d hd]; interval_cases d <;> simp [ha,hb,codeBit]; decide
    · refine ⟨0,by decide,?_⟩
      intro d hd; rw [bits d hd]; interval_cases d <;> simp [ha,hb,codeBit]
  refine ⟨mask,hm,?_⟩
  unfold Keys.star keyCorner
  rw [zero]
  have code : starCode (N k) 0 0 (neighbor F (origin k)) none =
      starCode (N k) 0 0 (fun d => if d=0 ∨ d=1 then (codeBit mask d).toNat else 9) none := by
    unfold starCode
    apply congrArg minimum; funext g
    have e (d : Nat) := eq (direction (invers g) d) (by unfold direction; omega)
    simp only [e]
  exact congrArg (fun c => 8*c+(decide (origin k∈F)).toNat) code

private theorem key_stable (k : Nat) (hk : 6≤k) (b : Nat) (hb : 6≤b)
    (mask : Nat) (f : Bool) : keyCorner (N k) mask f=keyCorner (N b) mask f := by
  have p (g : Fin 8) :
      fine (N k) 8 (transform g (N k) 0 0).1 (transform g (N k) 0 0).2 =
      fine (N b) 8 (transform g (N b) 0 0).1 (transform g (N b) 0 0).2 := by
    fin_cases g <;> norm_num [transform,fine,axis,clip,N,min_def,max_def] <;> split_ifs <;> omega
  unfold keyCorner
  apply congrArg (fun c => 8*c+f.toNat)
  unfold starCode
  apply congrArg minimum; funext g; simp only [p g]

private theorem mass_at (D : Chart) (F : Finset (Site k)) (o : Site k → Option (Fin 4))
    (x : Site k) {j} (found : locate D (index D) (Keys.star F o x)=some j) :
    (D.cols[j].units:Int)≤physicalVector D F o j := by
  have a := single_le_sum (s:=univ) (f:=fun t =>
    if locate D (index D) (Keys.star F o t)=some j then (D.cols[j].units:Int) else 0)
    (fun t _ => by split <;> positivity) (mem_univ x)
  rw [if_pos found] at a
  change _ ≤ scatter D (index D) (Keys.star F o) j at a
  unfold physicalVector counts
  have aux : 0≤(if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) := by
    split
    · exact le_max_left .. 
    · rfl
  linarith only [a,scatter_pos D (face F) j,scatter_pos D
    (fun t : Fin 8 × J k × J k => line F t.1 t.2.1 t.2.2) j,scatter_pos D (patch F) j,aux]

theorem decoded_corner {D : Chart} {b : Nat} (ok : checkCorner D (N b)) (hb : 6≤b)
    (F : Finset (Site k)) (hk : 6≤k) (acy : (G F).IsAcyclic) (t : Int) :
    ∃ i : Fin D.rows.size, i.val=0 ∧ rowHolds D.rows[i].sense
      (2*lhs D (physicalVector D F (out F)) i) (8*D.rows[i].rhs.atStep t) := by
  obtain ⟨mask,hm,eq⟩ := corner_key F (by omega) acy
  rw [key_stable k hk b hb] at eq
  obtain ⟨j,p,w⟩ := corner_lookup ok mask hm (decide (origin k∈F))
  rw [←eq] at p
  have lb := mass_at D F (out F) _ p
  unfold checkCorner at ok
  split at ok
  next h =>
    simp only [Id.run_pure,Bool.and_eq_true,beq_iff_eq,Array.all_eq_true_iff_forall_mem,
      decide_eq_true_eq] at ok
    let i : Fin D.rows.size := ⟨0,h⟩
    have pos (u : Fin D.cols.size) : 0≤coeff i D.cols[u].terms :=
      ok.1.2 _ (Array.getElem_mem u.isLt)
    have sm := single_le_sum (s:=univ) (f:=fun u : Fin D.cols.size =>
      coeff i D.cols[u].terms * physicalVector D F (out F) u)
      (fun u _ => mul_nonneg (pos u) (physical_nonneg ..)) (mem_univ j)
    have mul := mul_le_mul_of_nonneg_left lb (pos j)
    change coeff 0 _*_≤_ at mul
    rw [w] at mul
    refine ⟨i,rfl,?_⟩
    have sense : D.rows[i].sense=2 := ok.1.1.1
    have rhs : D.rows[i].rhs=⟨2,0,0⟩ := ok.1.1.2
    change rowHolds D.rows[i].sense _ (8*D.rows[i].rhs.atStep t)
    rw [sense,rhs]
    norm_num [rowHolds,Poly.atStep]
    change coeff 0 _*_≤lhs D _ i at sm
    exact by linarith only [le_trans mul sm]
  next => contradiction

abbrev cornerRow (D : Chart) (F : Finset (Site k)) (t : Int) := ∃ i : Fin D.rows.size,
  i.val=0 ∧ rowHolds D.rows[i].sense (2*lhs D (physicalVector D F (out F)) i)
    (8*D.rows[i].rhs.atStep t)

theorem corner19 (F : Finset (Site 6)) (acy : (G F).IsAcyclic) : cornerRow chart19 F 0 :=
  decoded_corner (b:=6) checked19 (by decide) F (by decide) acy 0

theorem corner58 (F : Finset (Site k)) (hk : 19≤k) (acy : (G F).IsAcyclic) (t : Int) :
    cornerRow chart58 F t :=
  decoded_corner (b:=19) checked58 (by decide) F (by omega) acy t

theorem corner61 (F : Finset (Site k)) (hk : 19≤k) (acy : (G F).IsAcyclic) (t : Int) :
    cornerRow chart61 F t :=
  decoded_corner (b:=20) checked61 (by decide) F (by omega) acy t

end GridGraphs.NoPitch.Budget
