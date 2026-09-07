import GridGraphs.Accounting.CarrierLayers.FourCarrier.ThreeOffside

/-! # Spaced positions and inclusive empty intervals

The bounds include intervals touching either end of the open side. Empty
left or right root sets are handled separately, not omitted from the count.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset

private theorem spaced_nonempty_card_bound (A : Finset Nat) (lo hi : Nat)
    (hne : A.Nonempty) (hbound : ∀ x ∈ A, lo ≤ x ∧ x ≤ hi)
    (hspace : ∀ x ∈ A, ∀ y ∈ A, x < y → x + 3 ≤ y) :
    3 * A.card + lo ≤ hi + 3 := by
  classical
  let f : A → Fin ((hi - lo) / 3 + 1) := fun x =>
    ⟨(x.val - lo) / 3, by have := hbound x.val x.property; omega⟩
  have hinj : Function.Injective f := by
    intro x y he
    have he' := congrArg Fin.val he
    have hx := hbound x.val x.property
    have hy := hbound y.val y.property
    dsimp [f] at he'
    apply Subtype.ext
    rcases lt_trichotomy x.val y.val with h | h | h
    · have := hspace x.val x.property y.val y.property h
      omega
    · exact h
    · have := hspace y.val y.property x.val x.property h
      omega
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_coe, Fintype.card_fin] at hc
  obtain ⟨x, hx⟩ := hne
  have := hbound x hx
  omega

/-- A quantitative empty-interval bound for `k-1` three-spaced positions.
The three numerical premises control the left end, right end, and internal
gaps respectively. Thus the same theorem covers end gaps. -/
theorem spaced_root_deficit_gap_bound {k g lo hi : Nat} (hk : 2 ≤ k)
    (A : Finset Nat) (hcard : A.card = k - 1)
    (hbound : ∀ x ∈ A, lo ≤ x ∧ x ≤ hi)
    (hspace : ∀ x ∈ A, ∀ y ∈ A, x < y → x + 3 ≤ y)
    (hleft : 6 ≤ lo + g) (hright : hi + 5 ≤ 3 * k + g)
    (hspan : hi + 8 ≤ 3 * k + lo + g)
    (a b : Nat) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3 * k)
    (hgap : ∀ x ∈ A, ¬ (a ≤ x ∧ x ≤ b)) : b - a + 1 ≤ g := by
  classical
  let L := A.filter (fun x => x < a)
  let R := A.filter (fun x => ¬ x < a)
  have hpart := card_filter_add_card_filter_not (s := A) (p := fun x => x < a)
  change L.card + R.card = A.card at hpart
  have hL (hne : L.Nonempty) : 3 * L.card + lo ≤ (a - 1) + 3 := by
    apply spaced_nonempty_card_bound L lo (a - 1) hne
    · intro x hx
      have hs := (mem_filter.mp hx).2
      have hx' := hbound x (mem_filter.mp hx).1
      omega
    · intro x hx y hy
      exact hspace x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
  have hR (hne : R.Nonempty) : 3 * R.card + (b + 1) ≤ hi + 3 := by
    apply spaced_nonempty_card_bound R (b + 1) hi hne
    · intro x hx
      have hs := (mem_filter.mp hx).2
      have hx' := hbound x (mem_filter.mp hx).1
      have hg := hgap x (mem_filter.mp hx).1
      omega
    · intro x hx y hy
      exact hspace x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
  by_cases hLe : L = ∅
  · have hLc : L.card = 0 := by simp [hLe]
    have hRn : R.Nonempty := card_pos.mp (by omega)
    have := hR hRn
    omega
  by_cases hRe : R = ∅
  · have hRc : R.card = 0 := by simp [hRe]
    have := hL (nonempty_iff_ne_empty.mpr hLe)
    omega
  · have := hL (nonempty_iff_ne_empty.mpr hLe)
    have := hR (nonempty_iff_ne_empty.mpr hRe)
    omega

end GridGraphs.CarrierLayers.FourCarrier
