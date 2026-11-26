import Mathlib
import GridGraphs.Constructions.ResidueTwo.LowerTurnKernel

/-! Reflective soundness of the three-dimensional integer-polyhedron
operations used to check local zipper turn certificates. Coefficients
stand for the tail parameter, row block and column block, respectively. -/
namespace GridGraphs.ResidueTwoLower.Poly

def Lin.val (a : Lin) (t i j : ℤ) := a.t*t+a.i*i+a.j*j+a.d

theorem Lin.entails_sound {a b : Lin} (h : a.entails b) (t i j) (ha : 0 ≤ a.val t i j) :
    0 ≤ b.val t i j := by
  simp [entails] at h
  obtain ⟨⟨⟨x,y⟩,z⟩,d⟩ := h
  simp [val,x,y,z] at ha ⊢
  omega

@[simp] theorem Lin.add_val (a b : Lin) (t i j) :
    (a.add b).val t i j = a.val t i j + b.val t i j := by simp [add,val]; ring
@[simp] theorem Lin.mul_val (k) (a : Lin) (t i j) :
    (a.mul k).val t i j = k*a.val t i j := by simp [mul,val]; ring
@[simp] theorem Lin.neg_nonneg (a : Lin) (t i j) :
    0 ≤ a.neg.val t i j ↔ ¬ 0 ≤ a.val t i j := by simp [val,neg]; omega
theorem Lin.den_val (a : Lin) (k t i j : ℤ) (hk : 0<k) (h : a.divides k=true) :
    (a.den k).val t i j = a.val t i j / k := by
  simp [divides] at h
  obtain ⟨⟨x,y⟩,z⟩ := h
  have ht := Int.ediv_mul_cancel x
  have hi := Int.ediv_mul_cancel y
  have hj := Int.ediv_mul_cancel z
  let q := (a.t/k)*t+(a.i/k)*i+(a.j/k)*j
  have id : a.val t i j = a.d+q*k := by
    dsimp [val,q]; linear_combination -t*ht-i*hi-j*hj
  rw [id,Int.add_mul_ediv_right _ _ (by omega)]
  simp [den,val,q]; ring

theorem Lin.norm_nonneg (a : Lin) (t i j) (h : 0 ≤ a.val t i j) :
    0 ≤ a.norm.val t i j := by
  unfold norm
  dsimp only
  split <;> rename_i g
  · simp at g
    rw [den_val _ _ _ _ _ (by omega) g.2]
    exact Int.ediv_nonneg h (by omega)
  · exact h

def Holds (p : List Lin) (t i j : ℤ) := ∀ a ∈ p, 0 ≤ a.val t i j

private theorem elim_sound {axis xs t i j} (h : Holds xs t i j) :
    Holds (elim axis xs) t i j := by
  intro a ha
  replace ha := (List.mem_filter.mp (show a∈(_ : List Lin).filter _ from ha)).1
  simp only [List.mem_eraseDups,List.mem_append,List.mem_filter,List.mem_flatMap,
    List.mem_map,decide_eq_true_eq,beq_iff_eq] at ha
  rcases ha with ⟨a',_⟩ | ⟨b,⟨hb,bp⟩,c,⟨hc,cn⟩,rfl⟩
  · exact h _ a'
  · apply Lin.norm_nonneg
    rw [Lin.add_val,Lin.mul_val,Lin.mul_val]
    exact add_nonneg (mul_nonneg (by omega) (h _ hb)) (mul_nonneg (by omega) (h _ hc))

private theorem clash_sound {xs t i j} (h : Holds xs t i j) : clash xs = false := by
  by_contra! neg
  simp only [Bool.not_eq_false,Bool.and_eq_true,clash,List.any_eq_true,
    beq_iff_eq,decide_eq_true_eq] at neg
  obtain ⟨a,ha,⟨⟨h₁,h₂⟩,h₃⟩,h₄⟩ := neg
  have := h a ha
  simp [Lin.val,h₁,h₂,h₃] at this
  omega

private theorem ordered_sound (x y z) {xs t i j} (h : Holds xs t i j) :
    ordered x y z xs = false := by
  simp [ordered,clash_sound (elim_sound h : Holds (elim x xs) t i j),
    clash_sound (elim_sound (elim_sound h) : Holds (elim y (elim x xs)) t i j),
    clash_sound (elim_sound (elim_sound (elim_sound h)) : Holds (elim z (elim y (elim x xs))) t i j)]

theorem impossible_sound {xs t i j} (h : Holds xs t i j) : impossible xs = false := by
  simp [impossible,clash_sound h,ordered_sound _ _ _ h]

theorem fallback_sound {xs t i j} (h : Holds xs t i j) : fallback xs = false := by
  simp [fallback,impossible_sound h,ordered_sound _ _ _ h]

end GridGraphs.ResidueTwoLower.Poly
