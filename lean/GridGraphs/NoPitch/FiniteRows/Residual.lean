import GridGraphs.NoPitch.Budget.RemainingRows
namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Budget Keys GridGraphs.NoPitch.Dual Finset
attribute [local irreducible] chart22 chart25 chart52

def residualOK (D : Chart) := decide (∀ j : Fin D.cols.size, 0<price D j →
  D.cols[j].units≤8 ∧ D.cols[j].key%8≤4 ∧ (D.cols[j].key%8=3 → D.cols[j].units≤1))
theorem residual25 : residualOK chart25 := by native_decide
theorem residual_census : repair chart22=0 ∧ repair chart52=0 ∧ repair chart25=1778 ∧
    (univ.filter fun j : Fin chart25.cols.size => 0<price chart25 j).card=1619 := by native_decide

theorem bounded_of_zero {D : Chart} (z : repair D=0) (j : Fin D.cols.size) : ¬0<price D j := by
  have pos (a : Fin D.cols.size) : 0≤price D a := by unfold price; split <;> first | rfl | exact le_max_left ..
  have h := single_le_sum (s:=univ) (f:=price D) (fun i _ => pos i) (mem_univ j)
  change _≤repair D at h; omega

/-- A positive-residual column receives mass from exactly one scatter.
Line mass uses all eight views but has unit weight. -/
theorem bounded {k} (D : Chart) (ok : residualOK D) (F : Finset (Site k)) (o : Site k → Option (Fin 4))
    (j : Fin D.cols.size) (h : 0<price D j) : physicalVector D F o j ≤ 8*(N k:Int)^2 := by
  obtain ⟨units,tag,lu⟩ := of_decide_eq_true ok j h
  let I := index D
  have cap {A : Type} [Fintype A] (f : A → Nat) : scatter D I f j≤(Fintype.card A:Int)*D.cols[j].units := by
    unfold scatter; rw [←nsmul_eq_mul]; apply le_trans (sum_le_sum (g:=fun _ => (D.cols[j].units:Int)) ?_)
    · simp
    · intro a _; split <;> simp
  have off {A : Type} [Fintype A] (f : A → Nat) (no : ∀ a, f a%8≠D.cols[j].key%8) : scatter D I f j=0 := by
    apply sum_eq_zero; intro a _; exact if_neg fun e => no a (congrArg (·%8) (locate_key e).symm)
  have ft (p : FacePos k) : face F p%8=2 := by unfold face faceCode keyAt; omega
  have pt (p : PatchPos k) : patch F p%8=4 := by unfold patch patchCode; omega
  let lineKey := fun t : Fin 8 × J k × J k => line F t.1 t.2.1 t.2.2
  have ltg t : lineKey t%8=3 := by unfold lineKey line; dsimp only; omega
  have st x : Keys.star F o x%8<2 := by unfold Keys.star; cases decide (x∈F) <;> simp
  have A := cap (Keys.star F o); have B := cap (face F); have C := cap lineKey; have E := cap (patch F)
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at A B C E
  have U : (D.cols[j].units:Int)≤8 := by exact_mod_cast units
  have nr : (0:Int)≤N k := by positivity
  have K : (k:Int)≤N k := by unfold N; omega
  have L : ((k+1:Nat):Int)≤N k := by unfold N; omega
  have P : ((N k-2:Nat):Int)≤N k := by omega
  change scatter D I (Keys.star F o) j+scatter D I (face F) j+scatter D I lineKey j+scatter D I (patch F) j+
    (if D.cols[j].key%8=5 then _ else 0)≤_
  rw [if_neg (by omega : D.cols[j].key%8≠5),add_zero]
  have Zf (e : D.cols[j].key%8≠2) := off (face F) (fun p => by rw [ft]; omega)
  have Zl (e : D.cols[j].key%8≠3) := off lineKey (fun p => by rw [ltg]; omega)
  have Zp (e : D.cols[j].key%8≠4) := off (patch F) (fun p => by rw [pt]; omega)
  have Zs (e : 2≤D.cols[j].key%8) := off (Keys.star F o) (fun p => by have := st p; omega)
  by_cases s : D.cols[j].key%8<2
  · simp only [Zf (by omega),Zl (by omega),Zp (by omega),add_zero]; grw [A,U]; ring_nf; rfl
  by_cases f : D.cols[j].key%8=2
  · simp only [Zs (by omega),Zl (by omega),Zp (by omega),zero_add,add_zero]; grw [B,U,K,K]; ring_nf; rfl
  by_cases l : D.cols[j].key%8=3
  · simp only [Zs (by omega),Zf (by omega),Zp (by omega),zero_add,add_zero]
    have W : (D.cols[j].units:Int)≤1 := by exact_mod_cast lu l
    grw [C,W,L,L]; ring_nf; rfl
  · simp only [Zs (by omega),Zf (by omega),Zl (by omega),zero_add]; grw [E,U,P,P]; ring_nf; rfl
end GridGraphs.NoPitch.FiniteRows
