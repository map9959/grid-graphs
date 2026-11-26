import GridGraphs.NoPitch.PhysicalKeys
import GridGraphs.NoPitch.SparseDual

namespace GridGraphs.NoPitch.Dual
open PitchCut Finset

abbrev Index := Std.HashMap Nat Nat
def index (D : Chart) : Index := Id.run do
  let mut m : Index := ∅
  for h : i in [:D.cols.size] do
    m := m.insert D.cols[i].key i
  return m

/-- An absent atom yields `none`; no default column receives its mass. -/
def locate (D : Chart) (m : Index) (key : Nat) : Option (Fin D.cols.size) := do
  let j ← m[key]?
  if h : j<D.cols.size then
    if D.cols[j].key=key then some ⟨j,h⟩ else none
  else none

theorem locate_key {D : Chart} {m key j} (found : locate D m key=some j) :
    D.cols[j].key=key := by
  unfold locate at found
  cases e : m[key]? with
  | none => simp [e] at found
  | some i =>
    simp [e] at found
    obtain ⟨_,hk,rfl⟩ := found
    exact hk

def unitCheck (D : Chart) := D.cols.all (fun c =>
  c.objective*c.units == (if c.key%8=1 then 8 else 0))

/-- Scatter stabilized counts directly into the decoded vector. -/
def scatter {I : Type*} [Fintype I] (D : Chart) (m : Index) (keys : I → Nat)
    (j : Fin D.cols.size) : Int :=
  ∑ i, if locate D m (keys i)=some j then (D.cols[j].units:Int) else 0

theorem scatter_score {I : Type*} [Fintype I] (D : Chart) (m : Index)
    (ok : unitCheck D) (keys : I → Nat) :
    score D (scatter D m keys)=
      ∑ i, (if (locate D m (keys i)).isSome && keys i%8==1 then 8 else 0 : Int) := by
  unfold score scatter
  simp_rw [mul_sum]; rw [sum_comm]
  apply sum_congr rfl; intro i _
  cases e : locate D m (keys i) with
  | none => simp
  | some j =>
    rw [sum_eq_single j]
    · have h := Array.all_eq_true_iff_forall_mem.mp ok _ (Array.getElem_mem j.isLt)
      have key := locate_key e
      rw [←key]
      simpa using (beq_iff_eq.mp h)
    · intro b _ ne; simp [Ne.symm ne]
    · simp

variable {k : Nat}

/-- Star, rank-face and directed floor-line portion of the physical vector.
The patch and complete-line coordinates are accounted separately. -/
noncomputable def counts (D : Chart) (m : Index) (F : Finset (Site k))
    (out : Site k → Option (Fin 4)) (j : Fin D.cols.size) :=
  scatter D m (Keys.star F out) j + scatter D m (Keys.face F) j +
    scatter D m (fun t : Fin 8 × Fin (k+1) × Fin (k+1) => Keys.line F t.1 t.2.1 t.2.2) j

theorem projected_score (D : Chart) (m : Index) (ok : unitCheck D) (F : Finset (Site k))
    (out : Site k → Option (Fin 4)) : score D (counts D m F out) =
    8*((F.filter (fun x => (locate D m (Keys.star F out x)).isSome)).card:Int) := by
  have add (a b : Fin D.cols.size → Int) : score D (fun j => a j+b j)=score D a+score D b := by
    simp [score,mul_add,sum_add_distrib]
  unfold counts
  rw [add,add,scatter_score _ _ ok,scatter_score _ _ ok,scatter_score _ _ ok]
  have face (p : FacePos k) : Keys.face F p%8≠1 := by unfold Keys.face Keys.faceCode Keys.keyAt; omega
  have line (g : Fin 8) (i j : Fin (k+1)) : Keys.line F g i j%8≠1 := by
    unfold Keys.line; dsimp only; omega
  simp only [beq_eq_false_iff_ne.mpr (face _),beq_eq_false_iff_ne.mpr (line _ _ _),
    Bool.and_false, Bool.false_eq_true,if_false,sum_const_zero,add_zero]
  have tag (x : Site k) : (Keys.star F out x%8==1)=decide (x∈F) := by
    unfold Keys.star; by_cases h : x∈F <;> simp [h]
  simp_rw [tag]
  let S := F.filter (fun x => (locate D m (Keys.star F out x)).isSome)
  calc
    _ = ∑ x : Site k, (if x∈S then 8 else 0 : Int) := by
      apply sum_congr rfl; intro x _; simp [S,and_comm]
    _ = _ := by change _=8*(S.card:Int); simp [mul_comm]

end GridGraphs.NoPitch.Dual
