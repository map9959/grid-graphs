import GridGraphs.Routing.CanonicalExpandedContourForest
import GridGraphs.Accounting.CheckerboardComponent

/-!
# Canonical demand phases

Canonical row or column demands are labelled by their index modulo three.  The
three corner demands are enumerated `northEast = 0`, `southEast = 1`, and
`southWest = 2`.  Thus, when `n = 3k+2`, phases zero and one each contain
`k+1` indexed demands and one corner, while phase two contains `k` indexed
demands and one corner.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalShoreDemand

/-- The natural three-phase label: indexed demands use their residue, and the
three distinguished corner demands retain their defining enumeration. -/
def phase {axis : ShoreSweepAxis} {n : Nat} :
    CanonicalShoreDemand axis n → Fin 3
  | .inl i => ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩
  | .inr c => c

@[simp] theorem phase_index {axis : ShoreSweepAxis} {n : Nat} (i : Fin n) :
    phase (axis := axis) (Sum.inl i : CanonicalShoreDemand axis n) =
      ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩ :=
  rfl

@[simp] theorem phase_northEast {axis : ShoreSweepAxis} {n : Nat} :
    phase (northEast : CanonicalShoreDemand axis n) = 0 := rfl

@[simp] theorem phase_southEast {axis : ShoreSweepAxis} {n : Nat} :
    phase (southEast : CanonicalShoreDemand axis n) = 1 := rfl

@[simp] theorem phase_southWest {axis : ShoreSweepAxis} {n : Nat} :
    phase (southWest : CanonicalShoreDemand axis n) = 2 := rfl

/-- Canonical demands of phase `p` whose boundary-incidence vertex is black. -/
def blackPhaseDemands {n : Nat} (axis : ShoreSweepAxis) (hn : 2 ≤ n) (p : Fin 3) :
    Finset (CanonicalShoreDemand axis n) :=
  Finset.univ.filter fun q =>
    phase q = p ∧ (boundaryIncidence axis hn q).1 ∈ gridBlack n n

/-- Canonical demands of phase `p` whose boundary-incidence vertex is white. -/
def whitePhaseDemands {n : Nat} (axis : ShoreSweepAxis) (hn : 2 ≤ n) (p : Fin 3) :
    Finset (CanonicalShoreDemand axis n) :=
  Finset.univ.filter fun q =>
    phase q = p ∧ (boundaryIncidence axis hn q).1 ∈ gridWhite n n

/-- Canonical demands whose boundary-incidence vertex is black. -/
def blackDemands {n : Nat} (axis : ShoreSweepAxis) (hn : 2 ≤ n) :
    Finset (CanonicalShoreDemand axis n) :=
  Finset.univ.filter fun q => (boundaryIncidence axis hn q).1 ∈ gridBlack n n

/-- Canonical demands whose boundary-incidence vertex is white. -/
def whiteDemands {n : Nat} (axis : ShoreSweepAxis) (hn : 2 ≤ n) :
    Finset (CanonicalShoreDemand axis n) :=
  Finset.univ.filter fun q => (boundaryIncidence axis hn q).1 ∈ gridWhite n n

private theorem card_fin_mod_six_lt (a b r : Nat) (hb : b ≤ 6) (hr : r < b) :
    ((Finset.univ : Finset (Fin (6 * a + b))).filter
      (fun i => i.val % 6 = r)).card = a + 1 := by
  let f : Fin (a + 1) → Fin (6 * a + b) := fun t => ⟨6 * t.val + r, by omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have := congrArg Fin.val hxy
    simp only [f] at this
    omega
  have himage :
      (Finset.univ : Finset (Fin (a + 1))).image f =
        (Finset.univ : Finset (Fin (6 * a + b))).filter
          (fun i => i.val % 6 = r) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      simp only [f]
      omega
    · intro hi
      have hdecomp := Nat.mod_add_div i.val 6
      refine ⟨⟨i.val / 6, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [f]
      omega
  rw [← himage, Finset.card_image_of_injective _ hf, Finset.card_univ,
    Fintype.card_fin]

private theorem card_fin_mod_six_ge (a b r : Nat) (hb : b ≤ r) (hr : r < 6) :
    ((Finset.univ : Finset (Fin (6 * a + b))).filter
      (fun i => i.val % 6 = r)).card = a := by
  let f : Fin a → Fin (6 * a + b) := fun t => ⟨6 * t.val + r, by omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have := congrArg Fin.val hxy
    simp only [f] at this
    omega
  have himage :
      (Finset.univ : Finset (Fin a)).image f =
        (Finset.univ : Finset (Fin (6 * a + b))).filter
          (fun i => i.val % 6 = r) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      simp only [f]
      omega
    · intro hi
      have hdecomp := Nat.mod_add_div i.val 6
      refine ⟨⟨i.val / 6, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [f]
      omega
  rw [← himage, Finset.card_image_of_injective _ hf, Finset.card_univ,
    Fintype.card_fin]

private theorem card_index_phase_zero (k : Nat) :
    ((Finset.univ : Finset (Fin (3 * k + 2))).filter
      (fun i => phase (axis := .rows)
        (Sum.inl i : CanonicalShoreDemand .rows (3 * k + 2)) = 0)).card =
      k + 1 := by
  let f : Fin (k + 1) → Fin (3 * k + 2) :=
    fun t => ⟨3 * t.val, by omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have := congrArg Fin.val hab
    simp only [f] at this
    omega
  have himage :
      (Finset.univ : Finset (Fin (k + 1))).image f =
        (Finset.univ : Finset (Fin (3 * k + 2))).filter
          (fun i => phase (axis := .rows)
            (Sum.inl i : CanonicalShoreDemand .rows (3 * k + 2)) = 0) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter,
      phase_index]
    constructor
    · rintro ⟨t, rfl⟩
      apply Fin.ext
      simp only [f]
      omega
    · intro hi
      have hrem : i.val % 3 = 0 := by
        simpa using congrArg Fin.val hi
      have hdecomp := Nat.mod_add_div i.val 3
      refine ⟨⟨i.val / 3, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [f]
      omega
  rw [← himage, Finset.card_image_of_injective _ hf, Finset.card_univ,
    Fintype.card_fin]

private theorem card_index_phase_one (k : Nat) :
    ((Finset.univ : Finset (Fin (3 * k + 2))).filter
      (fun i => phase (axis := .rows)
        (Sum.inl i : CanonicalShoreDemand .rows (3 * k + 2)) = 1)).card =
      k + 1 := by
  let f : Fin (k + 1) → Fin (3 * k + 2) :=
    fun t => ⟨3 * t.val + 1, by omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have := congrArg Fin.val hab
    simp only [f] at this
    omega
  have himage :
      (Finset.univ : Finset (Fin (k + 1))).image f =
        (Finset.univ : Finset (Fin (3 * k + 2))).filter
          (fun i => phase (axis := .rows)
            (Sum.inl i : CanonicalShoreDemand .rows (3 * k + 2)) = 1) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter,
      phase_index]
    constructor
    · rintro ⟨t, rfl⟩
      apply Fin.ext
      simp only [f]
      omega
    · intro hi
      have hrem : i.val % 3 = 1 := by
        simpa using congrArg Fin.val hi
      have hdecomp := Nat.mod_add_div i.val 3
      refine ⟨⟨i.val / 3, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [f]
      omega
  rw [← himage, Finset.card_image_of_injective _ hf, Finset.card_univ,
    Fintype.card_fin]

private theorem card_index_phase_two (k : Nat) :
    ((Finset.univ : Finset (Fin (3 * k + 2))).filter
      (fun i => phase (axis := .rows)
        (Sum.inl i : CanonicalShoreDemand .rows (3 * k + 2)) = 2)).card =
      k := by
  let f : Fin k → Fin (3 * k + 2) :=
    fun t => ⟨3 * t.val + 2, by omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have := congrArg Fin.val hab
    simp only [f] at this
    omega
  have himage :
      (Finset.univ : Finset (Fin k)).image f =
        (Finset.univ : Finset (Fin (3 * k + 2))).filter
          (fun i => phase (axis := .rows)
            (Sum.inl i : CanonicalShoreDemand .rows (3 * k + 2)) = 2) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter,
      phase_index]
    constructor
    · rintro ⟨t, rfl⟩
      apply Fin.ext
      simp only [f]
      omega
    · intro hi
      have hrem : i.val % 3 = 2 := by
        simpa using congrArg Fin.val hi
      have hdecomp := Nat.mod_add_div i.val 3
      refine ⟨⟨i.val / 3, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [f]
      omega
  rw [← himage, Finset.card_image_of_injective _ hf, Finset.card_univ,
    Fintype.card_fin]

/-- For `n = 3k+2`, phase zero consists of `k+1` indexed demands and the
north-east corner. -/
theorem card_phase_zero (axis : ShoreSweepAxis) (k : Nat) :
    ((Finset.univ : Finset (CanonicalShoreDemand axis (3 * k + 2))).filter
      (fun q => phase q = 0)).card = k + 2 := by
  have hsplit :
      (Finset.univ.filter (fun q : CanonicalShoreDemand axis (3 * k + 2) => phase q = 0)) =
        (Finset.univ.filter (fun i : Fin (3 * k + 2) =>
          phase (axis := axis) (Sum.inl i) = 0)).disjSum
        (Finset.univ.filter (fun c : Fin 3 =>
          phase (axis := axis)
            (Sum.inr c : CanonicalShoreDemand axis (3 * k + 2)) = 0)) := by
    ext q
    rcases q with i | c
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, phase]
      rw [Finset.inl_mem_disjSum]
      simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, phase]
      rw [Finset.inr_mem_disjSum]
      simp
  rw [hsplit, Finset.card_disjSum]
  have hindex := card_index_phase_zero k
  change _ + _ = k + 2
  rw [show (Finset.univ.filter (fun i : Fin (3 * k + 2) =>
    phase (axis := axis) (Sum.inl i) = 0)).card = k + 1 by
      simpa only [phase_index] using hindex]
  have hcorner : (Finset.univ.filter (fun c : Fin 3 => c = 0)) = {0} := by
    ext c
    simp
  change k + 1 + (Finset.univ.filter (fun c : Fin 3 => c = 0)).card = k + 2
  simp [hcorner]

/-- For `n = 3k+2`, phase one consists of `k+1` indexed demands and the
south-east corner. -/
theorem card_phase_one (axis : ShoreSweepAxis) (k : Nat) :
    ((Finset.univ : Finset (CanonicalShoreDemand axis (3 * k + 2))).filter
      (fun q => phase q = 1)).card = k + 2 := by
  have hsplit :
      (Finset.univ.filter (fun q : CanonicalShoreDemand axis (3 * k + 2) => phase q = 1)) =
        (Finset.univ.filter (fun i : Fin (3 * k + 2) =>
          phase (axis := axis) (Sum.inl i) = 1)).disjSum
        (Finset.univ.filter (fun c : Fin 3 =>
          phase (axis := axis)
            (Sum.inr c : CanonicalShoreDemand axis (3 * k + 2)) = 1)) := by
    ext q
    rcases q with i | c
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, phase]
      rw [Finset.inl_mem_disjSum]
      simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, phase]
      rw [Finset.inr_mem_disjSum]
      simp
  rw [hsplit, Finset.card_disjSum]
  have hindex := card_index_phase_one k
  change _ + _ = k + 2
  rw [show (Finset.univ.filter (fun i : Fin (3 * k + 2) =>
    phase (axis := axis) (Sum.inl i) = 1)).card = k + 1 by
      simpa only [phase_index] using hindex]
  have hcorner : (Finset.univ.filter (fun c : Fin 3 => c = 1)) = {1} := by
    ext c
    simp
  change k + 1 + (Finset.univ.filter (fun c : Fin 3 => c = 1)).card = k + 2
  simp [hcorner]

/-- For `n = 3k+2`, phase two consists of `k` indexed demands and the
south-west corner. -/
theorem card_phase_two (axis : ShoreSweepAxis) (k : Nat) :
    ((Finset.univ : Finset (CanonicalShoreDemand axis (3 * k + 2))).filter
      (fun q => phase q = 2)).card = k + 1 := by
  have hsplit :
      (Finset.univ.filter (fun q : CanonicalShoreDemand axis (3 * k + 2) => phase q = 2)) =
        (Finset.univ.filter (fun i : Fin (3 * k + 2) =>
          phase (axis := axis) (Sum.inl i) = 2)).disjSum
        (Finset.univ.filter (fun c : Fin 3 =>
          phase (axis := axis)
            (Sum.inr c : CanonicalShoreDemand axis (3 * k + 2)) = 2)) := by
    ext q
    rcases q with i | c
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, phase]
      rw [Finset.inl_mem_disjSum]
      simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, phase]
      rw [Finset.inr_mem_disjSum]
      simp
  rw [hsplit, Finset.card_disjSum]
  have hindex := card_index_phase_two k
  change _ + _ = k + 1
  rw [show (Finset.univ.filter (fun i : Fin (3 * k + 2) =>
    phase (axis := axis) (Sum.inl i) = 2)).card = k by
      simpa only [phase_index] using hindex]
  have hcorner : (Finset.univ.filter (fun c : Fin 3 => c = 2)) = {2} := by
    ext c
    simp
  change k + (Finset.univ.filter (fun c : Fin 3 => c = 2)).card = k + 1
  simp [hcorner]

private theorem card_blackPhaseDemands_split {n : Nat} (axis : ShoreSweepAxis)
    (hn : 2 ≤ n) (p : Fin 3) :
    (blackPhaseDemands axis hn p).card =
      ((Finset.univ : Finset (Fin n)).filter fun i =>
        phase (axis := axis) (Sum.inl i) = p ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈ gridBlack n n).card +
      ((Finset.univ : Finset (Fin 3)).filter fun c =>
        phase (axis := axis) (Sum.inr c : CanonicalShoreDemand axis n) = p ∧
          (boundaryIncidence axis hn
            (Sum.inr c : CanonicalShoreDemand axis n)).1 ∈ gridBlack n n).card := by
  rw [← Finset.card_disjSum]
  congr 1
  ext q
  rcases q with i | c
  · simp only [blackPhaseDemands, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.inl_mem_disjSum]
    simp
  · simp only [blackPhaseDemands, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.inr_mem_disjSum]
    simp

private theorem card_black_add_white_phase {n : Nat} (axis : ShoreSweepAxis)
    (hn : 2 ≤ n) (p : Fin 3) :
    (blackPhaseDemands axis hn p).card + (whitePhaseDemands axis hn p).card =
      ((Finset.univ : Finset (CanonicalShoreDemand axis n)).filter
        fun q => phase q = p).card := by
  have hdisjoint : Disjoint (blackPhaseDemands axis hn p)
      (whitePhaseDemands axis hn p) := by
    rw [Finset.disjoint_left]
    intro q hqB hqW
    simp only [blackPhaseDemands, whitePhaseDemands, Finset.mem_filter,
      Finset.mem_univ, true_and] at hqB hqW
    exact (Finset.mem_sdiff.mp hqW.2).2 hqB.2
  rw [← Finset.card_union_of_disjoint hdisjoint]
  congr 1
  ext q
  simp only [blackPhaseDemands, whitePhaseDemands, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨hp, -⟩ | ⟨hp, -⟩)
    · exact hp
    · exact hp
  · intro hp
    by_cases hblack : (boundaryIncidence axis hn q).1 ∈ gridBlack n n
    · exact Or.inl ⟨hp, hblack⟩
    · exact Or.inr ⟨hp, by simpa [gridWhite] using hblack⟩

private theorem card_black_index_even (axis : ShoreSweepAxis) (a : Nat) :
    let hn : 2 ≤ 3 * (2 * a) + 2 := by omega
    (((Finset.univ : Finset (Fin (3 * (2 * a) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 0 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)).card = a + 1) ∧
    (((Finset.univ : Finset (Fin (3 * (2 * a) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 1 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)).card = a) ∧
    ((Finset.univ : Finset (Fin (3 * (2 * a) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 2 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)).card = a := by
  intro hn
  have hzero :
      ((Finset.univ : Finset (Fin (3 * (2 * a) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 0 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)) =
      (Finset.univ : Finset (Fin (3 * (2 * a) + 2))).filter
        (fun i => i.val % 6 = 0) := by
    ext i
    cases axis <;> simp [phase, boundaryIncidence, gridBlack] <;> omega
  have hone :
      ((Finset.univ : Finset (Fin (3 * (2 * a) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 1 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)) =
      (Finset.univ : Finset (Fin (3 * (2 * a) + 2))).filter
        (fun i => i.val % 6 = 4) := by
    ext i
    cases axis <;> simp [phase, boundaryIncidence, gridBlack] <;> omega
  have htwo :
      ((Finset.univ : Finset (Fin (3 * (2 * a) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 2 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)) =
      (Finset.univ : Finset (Fin (3 * (2 * a) + 2))).filter
        (fun i => i.val % 6 = 2) := by
    ext i
    have hmod := Nat.mod_lt i.val (by omega : 0 < 6)
    have hmod2 := Nat.mod_mod_of_dvd i.val (by omega : 2 ∣ 6)
    have hmod3 := Nat.mod_mod_of_dvd i.val (by omega : 3 ∣ 6)
    have harith : (i.val % 3 = 2 ∧ i.val % 2 = 0) ↔ i.val % 6 = 2 := by
      rw [← hmod2, ← hmod3]
      interval_cases h : i.val % 6 <;> omega
    cases axis <;>
      simpa [phase, boundaryIncidence, gridBlack, Fin.ext_iff] using harith
  rw [hzero, hone, htwo]
  rw [show 3 * (2 * a) + 2 = 6 * a + 2 by omega]
  exact ⟨card_fin_mod_six_lt a 2 0 (by omega) (by omega),
    card_fin_mod_six_ge a 2 4 (by omega) (by omega),
    card_fin_mod_six_ge a 2 2 (by omega) (by omega)⟩

private theorem card_black_index_odd (axis : ShoreSweepAxis) (a : Nat) :
    let hn : 2 ≤ 3 * (2 * a + 1) + 2 := by omega
    (((Finset.univ : Finset (Fin (3 * (2 * a + 1) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 0 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2)).card = a + 1) ∧
    (((Finset.univ : Finset (Fin (3 * (2 * a + 1) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 1 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2)).card = a + 1) ∧
    ((Finset.univ : Finset (Fin (3 * (2 * a + 1) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 2 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2)).card = a + 1 := by
  intro hn
  have hzero :
      ((Finset.univ : Finset (Fin (3 * (2 * a + 1) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 0 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2)) =
      (Finset.univ : Finset (Fin (3 * (2 * a + 1) + 2))).filter
        (fun i => i.val % 6 = 0) := by
    ext i
    cases axis <;> simp [phase, boundaryIncidence, gridBlack] <;> omega
  have hone :
      ((Finset.univ : Finset (Fin (3 * (2 * a + 1) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 1 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2)) =
      (Finset.univ : Finset (Fin (3 * (2 * a + 1) + 2))).filter
        (fun i => i.val % 6 = 4) := by
    ext i
    cases axis <;> simp [phase, boundaryIncidence, gridBlack] <;> omega
  have htwo :
      ((Finset.univ : Finset (Fin (3 * (2 * a + 1) + 2))).filter fun i =>
        phase (axis := axis) (Sum.inl i) = 2 ∧
          (boundaryIncidence axis hn (Sum.inl i)).1 ∈
            gridBlack (3 * (2 * a + 1) + 2) (3 * (2 * a + 1) + 2)) =
      (Finset.univ : Finset (Fin (3 * (2 * a + 1) + 2))).filter
        (fun i => i.val % 6 = 2) := by
    ext i
    have hmod := Nat.mod_lt i.val (by omega : 0 < 6)
    have hmod2 := Nat.mod_mod_of_dvd i.val (by omega : 2 ∣ 6)
    have hmod3 := Nat.mod_mod_of_dvd i.val (by omega : 3 ∣ 6)
    have harith : (i.val % 3 = 2 ∧ i.val % 2 = 0) ↔ i.val % 6 = 2 := by
      rw [← hmod2, ← hmod3]
      interval_cases h : i.val % 6 <;> omega
    cases axis <;>
      simpa [phase, boundaryIncidence, gridBlack, Fin.ext_iff] using harith
  rw [hzero, hone, htwo]
  rw [show 3 * (2 * a + 1) + 2 = 6 * a + 5 by omega]
  exact ⟨card_fin_mod_six_lt a 5 0 (by omega) (by omega),
    card_fin_mod_six_lt a 5 4 (by omega) (by omega),
    card_fin_mod_six_lt a 5 2 (by omega) (by omega)⟩

/-- If `k = 2a`, the six phase/color fibers have sizes
`(a+1,a+1)`, `(a+1,a+1)`, and `(a,a+1)` (black, white). -/
theorem card_phase_colors_even (axis : ShoreSweepAxis) (a : Nat) :
    let hn : 2 ≤ 3 * (2 * a) + 2 := by omega
    (blackPhaseDemands axis hn 0).card = a + 1 ∧
    (whitePhaseDemands axis hn 0).card = a + 1 ∧
    (blackPhaseDemands axis hn 1).card = a + 1 ∧
    (whitePhaseDemands axis hn 1).card = a + 1 ∧
    (blackPhaseDemands axis hn 2).card = a ∧
    (whitePhaseDemands axis hn 2).card = a + 1 := by
  intro hn
  have hi := card_black_index_even axis a
  rcases hi with ⟨hi0, hi1, hi2⟩
  have hc0 :
      ((Finset.univ : Finset (Fin 3)).filter fun c =>
        phase (axis := axis)
            (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a) + 2)) = 0 ∧
          (boundaryIncidence axis hn
            (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a) + 2))).1 ∈
              gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)).card = 0 := by
    rw [Finset.card_eq_zero]
    ext c
    cases axis <;> fin_cases c <;>
      simp [phase, boundaryIncidence, gridBlack] <;> omega
  have hc1 :
      ((Finset.univ : Finset (Fin 3)).filter fun c =>
        phase (axis := axis)
            (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a) + 2)) = 1 ∧
          (boundaryIncidence axis hn
            (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a) + 2))).1 ∈
              gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)).card = 1 := by
    have hset :
        ((Finset.univ : Finset (Fin 3)).filter fun c =>
          phase (axis := axis)
              (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a) + 2)) = 1 ∧
            (boundaryIncidence axis hn
              (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a) + 2))).1 ∈
                gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)) = {1} := by
      ext c
      cases axis <;> fin_cases c <;>
        simp [phase, boundaryIncidence, gridBlack] <;> omega
    rw [hset]
    simp
  have hc2 :
      ((Finset.univ : Finset (Fin 3)).filter fun c =>
        phase (axis := axis)
            (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a) + 2)) = 2 ∧
          (boundaryIncidence axis hn
            (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a) + 2))).1 ∈
              gridBlack (3 * (2 * a) + 2) (3 * (2 * a) + 2)).card = 0 := by
    rw [Finset.card_eq_zero]
    ext c
    cases axis <;> fin_cases c <;>
      simp [phase, boundaryIncidence, gridBlack] <;> omega
  have hb0 : (blackPhaseDemands axis hn 0).card = a + 1 := by
    rw [card_blackPhaseDemands_split axis hn 0, hi0, hc0]
  have hb1 : (blackPhaseDemands axis hn 1).card = a + 1 := by
    rw [card_blackPhaseDemands_split axis hn 1, hi1, hc1]
  have hb2 : (blackPhaseDemands axis hn 2).card = a := by
    rw [card_blackPhaseDemands_split axis hn 2, hi2, hc2]
    omega
  have hp0 := card_black_add_white_phase axis hn 0
  have hp1 := card_black_add_white_phase axis hn 1
  have hp2 := card_black_add_white_phase axis hn 2
  rw [card_phase_zero axis (2 * a), hb0] at hp0
  rw [card_phase_one axis (2 * a), hb1] at hp1
  rw [card_phase_two axis (2 * a), hb2] at hp2
  exact ⟨hb0, by omega, hb1, by omega, hb2, by omega⟩

/-- If `k = 2a+1`, the black phase fibers all have size `a+2`; the white
phase fibers have sizes `a+1`, `a+1`, and `a`. -/
theorem card_phase_colors_odd (axis : ShoreSweepAxis) (a : Nat) :
    let hn : 2 ≤ 3 * (2 * a + 1) + 2 := by omega
    (blackPhaseDemands axis hn 0).card = a + 2 ∧
    (whitePhaseDemands axis hn 0).card = a + 1 ∧
    (blackPhaseDemands axis hn 1).card = a + 2 ∧
    (whitePhaseDemands axis hn 1).card = a + 1 ∧
    (blackPhaseDemands axis hn 2).card = a + 2 ∧
    (whitePhaseDemands axis hn 2).card = a := by
  intro hn
  have hi := card_black_index_odd axis a
  rcases hi with ⟨hi0, hi1, hi2⟩
  have hc (p : Fin 3) :
      ((Finset.univ : Finset (Fin 3)).filter fun c =>
        phase (axis := axis)
            (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a + 1) + 2)) = p ∧
          (boundaryIncidence axis hn
            (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a + 1) + 2))).1 ∈
              gridBlack (3 * (2 * a + 1) + 2)
                (3 * (2 * a + 1) + 2)).card = 1 := by
    have hset :
        ((Finset.univ : Finset (Fin 3)).filter fun c =>
          phase (axis := axis)
              (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a + 1) + 2)) = p ∧
            (boundaryIncidence axis hn
              (Sum.inr c : CanonicalShoreDemand axis (3 * (2 * a + 1) + 2))).1 ∈
                gridBlack (3 * (2 * a + 1) + 2)
                  (3 * (2 * a + 1) + 2)) = {p} := by
      ext c
      cases axis <;> fin_cases p <;> fin_cases c <;>
        simp [phase, boundaryIncidence, gridBlack] <;> omega
    rw [hset]
    simp
  have hb0 : (blackPhaseDemands axis hn 0).card = a + 2 := by
    rw [card_blackPhaseDemands_split axis hn 0, hi0, hc 0]
  have hb1 : (blackPhaseDemands axis hn 1).card = a + 2 := by
    rw [card_blackPhaseDemands_split axis hn 1, hi1, hc 1]
  have hb2 : (blackPhaseDemands axis hn 2).card = a + 2 := by
    rw [card_blackPhaseDemands_split axis hn 2, hi2, hc 2]
  have hp0 := card_black_add_white_phase axis hn 0
  have hp1 := card_black_add_white_phase axis hn 1
  have hp2 := card_black_add_white_phase axis hn 2
  rw [card_phase_zero axis (2 * a + 1), hb0] at hp0
  rw [card_phase_one axis (2 * a + 1), hb1] at hp1
  rw [card_phase_two axis (2 * a + 1), hb2] at hp2
  exact ⟨hb0, by omega, hb1, by omega, hb2, by omega⟩

private theorem card_blackDemands_eq_sum_phases {n : Nat} (axis : ShoreSweepAxis)
    (hn : 2 ≤ n) :
    (blackDemands axis hn).card =
      ∑ p : Fin 3, (blackPhaseDemands axis hn p).card := by
  have hf (p : Fin 3) :
      ((blackDemands axis hn).filter fun q => phase q = p) =
        blackPhaseDemands axis hn p := by
    ext q
    simp [blackDemands, blackPhaseDemands, and_comm]
  calc
    (blackDemands axis hn).card =
        ∑ p ∈ (Finset.univ : Finset (Fin 3)),
          ((blackDemands axis hn).filter fun q => phase q = p).card := by
      symm
      simpa using Finset.sum_card_fiberwise_eq_card_filter
        (blackDemands axis hn) (Finset.univ : Finset (Fin 3)) phase
    _ = ∑ p : Fin 3, (blackPhaseDemands axis hn p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hf]

private theorem card_whiteDemands_eq_sum_phases {n : Nat} (axis : ShoreSweepAxis)
    (hn : 2 ≤ n) :
    (whiteDemands axis hn).card =
      ∑ p : Fin 3, (whitePhaseDemands axis hn p).card := by
  have hf (p : Fin 3) :
      ((whiteDemands axis hn).filter fun q => phase q = p) =
        whitePhaseDemands axis hn p := by
    ext q
    simp [whiteDemands, whitePhaseDemands, and_comm]
  calc
    (whiteDemands axis hn).card =
        ∑ p ∈ (Finset.univ : Finset (Fin 3)),
          ((whiteDemands axis hn).filter fun q => phase q = p).card := by
      symm
      simpa using Finset.sum_card_fiberwise_eq_card_filter
        (whiteDemands axis hn) (Finset.univ : Finset (Fin 3)) phase
    _ = ∑ p : Fin 3, (whitePhaseDemands axis hn p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hf]

/-- For `k = 2a`, there are `3a+2` black and `3a+3` white canonical demands. -/
theorem card_colors_even (axis : ShoreSweepAxis) (a : Nat) :
    let hn : 2 ≤ 3 * (2 * a) + 2 := by omega
    (blackDemands axis hn).card = 3 * a + 2 ∧
      (whiteDemands axis hn).card = 3 * a + 3 := by
  intro hn
  rcases card_phase_colors_even axis a with
    ⟨hb0, hw0, hb1, hw1, hb2, hw2⟩
  have hb := card_blackDemands_eq_sum_phases axis hn
  have hw := card_whiteDemands_eq_sum_phases axis hn
  rw [Fin.sum_univ_three, hb0, hb1, hb2] at hb
  rw [Fin.sum_univ_three, hw0, hw1, hw2] at hw
  omega

/-- For `k = 2a+1`, there are `3a+6` black and `3a+2` white canonical demands. -/
theorem card_colors_odd (axis : ShoreSweepAxis) (a : Nat) :
    let hn : 2 ≤ 3 * (2 * a + 1) + 2 := by omega
    (blackDemands axis hn).card = 3 * a + 6 ∧
      (whiteDemands axis hn).card = 3 * a + 2 := by
  intro hn
  rcases card_phase_colors_odd axis a with
    ⟨hb0, hw0, hb1, hw1, hb2, hw2⟩
  have hb := card_blackDemands_eq_sum_phases axis hn
  have hw := card_whiteDemands_eq_sum_phases axis hn
  rw [Fin.sum_univ_three, hb0, hb1, hb2] at hb
  rw [Fin.sum_univ_three, hw0, hw1, hw2] at hw
  omega

end CanonicalShoreDemand

namespace CanonicalExpandedContourForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Recover the unique canonical demand represented by a first-stop start. -/
def demandOfStart
    (s : ↥(firstStop axis hn2 hT).starts) : CanonicalShoreDemand axis n :=
  demandOfStartSlot axis hn2 hT
    ⟨s.1, s.2⟩

@[simp] theorem startSlot_demandOfStart
    (s : ↥(firstStop axis hn2 hT).starts) :
    startSlot axis hn2 hT (demandOfStart axis hn2 hT s) = s.1 := by
  exact startSlot_demandOfStartSlot axis hn2 hT
    ⟨s.1, s.2⟩

/-- Starts and canonical demands are canonically equivalent once start slots
are known to be distinct. -/
def demandOfStartEquiv (hn3 : 3 ≤ n) :
    ↥(firstStop axis hn2 hT).starts ≃ CanonicalShoreDemand axis n where
  toFun := demandOfStart axis hn2 hT
  invFun q := ⟨startSlot axis hn2 hT q, by
    simp [firstStop, startSlots]⟩
  left_inv s := by
    apply Subtype.ext
    exact startSlot_demandOfStart axis hn2 hT s
  right_inv q := by
    apply (demand_eq_demandOfStartSlot axis hn2 hT hn3
      ⟨startSlot axis hn2 hT q, by simp [startSlots]⟩ q rfl).symm

/-- Origins at one reached exit whose unique canonical demands have phase `p`. -/
def phaseOrigins (p : Fin 3) (x : (firstStop axis hn2 hT).State) :
    Finset ↥(firstStop axis hn2 hT).starts :=
  ((firstStop axis hn2 hT).origins x).filter fun s =>
    CanonicalShoreDemand.phase (demandOfStart axis hn2 hT s) = p

/-- Summing a phase fiber over all reached exits recovers the global canonical
demand phase fiber. -/
theorem sum_card_phaseOrigins (hn3 : 3 ≤ n) (p : Fin 3) :
    ∑ x ∈ (firstStop axis hn2 hT).reachedStops,
        (phaseOrigins axis hn2 hT p x).card =
      ((Finset.univ : Finset (CanonicalShoreDemand axis n)).filter fun q =>
        CanonicalShoreDemand.phase q = p).card := by
  let F := firstStop axis hn2 hT
  let w : ↥F.starts → Nat := fun s =>
    if CanonicalShoreDemand.phase (demandOfStart axis hn2 hT s) = p then 1 else 0
  have hpartition := F.sum_origins_reachedStops w
  have hreindex :
      (∑ s, w s) =
        ∑ q : CanonicalShoreDemand axis n,
          if CanonicalShoreDemand.phase q = p then 1 else 0 := by
    apply Fintype.sum_equiv (demandOfStartEquiv axis hn2 hT hn3)
    intro s
    rfl
  rw [hreindex] at hpartition
  simpa [F, w, phaseOrigins] using hpartition

/-- A canonical expanded start is based at its original boundary-incidence
vertex, whether it is a direct outer slot or a retained inward dart. -/
@[simp] theorem startSlot_vertex {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (q : CanonicalShoreDemand axis n) :
    (startSlot axis hn2 hT q).1 =
      (CanonicalShoreDemand.boundaryIncidence axis hn2 q).1 := by
  classical
  by_cases hq : q ∈ CanonicalShoreDemand.directExits axis hn2 T
  · simp [startSlot, hq, GridExpandedContour.outerPortSlot]
  · simp [startSlot, hq, GridExpandedContour.slotOfDart,
      GridDirectionalDart.retainedCanonicalInwardDart]

/-- At `n = 3k+2`, phase-zero origin counts over reached exits sum to `k+2`. -/
theorem sum_card_phaseOrigins_zero (axis : ShoreSweepAxis) (k : Nat)
    (hn3 : 3 ≤ 3 * k + 2)
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T) :
    ∑ x ∈ (firstStop axis (by omega) hT).reachedStops,
        (phaseOrigins axis (by omega) hT 0 x).card = k + 2 := by
  rw [sum_card_phaseOrigins axis (by omega) hT hn3 0,
    CanonicalShoreDemand.card_phase_zero]

/-- At `n = 3k+2`, phase-one origin counts over reached exits sum to `k+2`. -/
theorem sum_card_phaseOrigins_one (axis : ShoreSweepAxis) (k : Nat)
    (hn3 : 3 ≤ 3 * k + 2)
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T) :
    ∑ x ∈ (firstStop axis (by omega) hT).reachedStops,
        (phaseOrigins axis (by omega) hT 1 x).card = k + 2 := by
  rw [sum_card_phaseOrigins axis (by omega) hT hn3 1,
    CanonicalShoreDemand.card_phase_one]

/-- At `n = 3k+2`, phase-two origin counts over reached exits sum to `k+1`. -/
theorem sum_card_phaseOrigins_two (axis : ShoreSweepAxis) (k : Nat)
    (hn3 : 3 ≤ 3 * k + 2)
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T) :
    ∑ x ∈ (firstStop axis (by omega) hT).reachedStops,
        (phaseOrigins axis (by omega) hT 2 x).card = k + 1 := by
  rw [sum_card_phaseOrigins axis (by omega) hT hn3 2,
    CanonicalShoreDemand.card_phase_two]

end

end CanonicalExpandedContourForest

namespace GridExpandedContour

/-- An occupied expanded successor crosses one grid edge and swaps
checkerboard color. -/
theorem succ_vertex_mem_black_iff_not_of_occupied {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : T ≤ gridGraph m n) {s : GridCompassSlot m n}
    (hs : Occupied (T := T) s) :
    (succ (T := T) s).1 ∈ gridBlack m n ↔ s.1 ∉ gridBlack m n := by
  rw [succ_of_occupied hs]
  exact grid_adj_mem_black_iff_not_mem_black
    (hT (GridDirectionalDart.ofDirectionMem (T := T) s.1 s.2 hs).adj).symm

/-- An unoccupied expanded successor turns in place and preserves checkerboard
color. -/
theorem succ_vertex_mem_black_iff_of_not_occupied {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    {s : GridCompassSlot m n} (hs : ¬Occupied (T := T) s) :
    (succ (T := T) s).1 ∈ gridBlack m n ↔ s.1 ∈ gridBlack m n := by
  rw [succ_of_not_occupied hs]

end GridExpandedContour

end GridGraphs
