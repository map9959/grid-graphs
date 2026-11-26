import GridGraphs.Constructions.ResidueTwo.LowerZipperRows

namespace GridGraphs.ResidueTwoLower

/-- Count a truncated pitch-three run using only division of its endpoints. -/
theorem rowCount_pitch (a b d w : Nat) (hab : a ≤ b) (hd : d<3) :
    rowCount (fun j => a ≤ j && j < b && j%3 == d) w =
    ((min w b + (2-d))/3) - ((min w a + (2-d))/3) := by
  induction w with
  | zero => simp [rowCount]
  | succ w ih =>
    rw [rowCount_succ,ih]
    simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    split <;> omega

theorem rowCount_or (p q : Nat → Bool) {w : Nat}
    (dis : ∀ j < w, p j = true → q j = false) :
    rowCount (fun c => p c || q c) w = rowCount p w + rowCount q w := by
  induction w with
  | zero => simp [rowCount]
  | succ w ih =>
    rw [rowCount_succ,ih (fun j hj => dis j (by omega)),rowCount_succ,rowCount_succ]
    specialize dis w (by omega)
    cases h : p w <;> cases h' : q w <;> simp_all <;> omega

theorem rowCount_congr {p q : Nat → Bool} {w : Nat}
    (h : ∀ j < w, p j = q j) : rowCount p w = rowCount q w := by
  unfold rowCount
  congr 1
  apply Finset.filter_congr
  simpa using h

theorem rowCount_wire_add (p : Nat → Bool) {w j : Nat} (hj : j<w) (hp : p j=false) :
    rowCount (fun c => p c || c == j) w = rowCount p w + 1 := by
  have e : (Finset.range w).filter (fun c => p c || c == j) =
      insert j ((Finset.range w).filter (fun c => p c)) := by
    ext c
    simp
    grind
  unfold rowCount
  rw [e,Finset.card_insert_of_notMem (by simp [hp])]

theorem rowCount_wire_remove (p : Nat → Bool) {w j : Nat} (hj : j<w) (hp : p j=true) :
    rowCount (fun c => p c && c != j) w + 1 = rowCount p w := by
  have e : (fun c => (p c && c != j) || c == j) = p := by
    funext c
    by_cases h : c=j
    · subst c; simp [hp]
    · have hh : (c == j) = false := by simpa using h
      simp [bne,hh]
  rw [← rowCount_wire_add (fun c => p c && c != j) hj (by simp), e]

end GridGraphs.ResidueTwoLower
