import Mathlib

namespace GridGraphs.FoldedStripCover

/-- Arbitrary intermediate states of a homogeneous physical transition.
No equality between endpoints and no repeated mask is required. -/
inductive Walk {S : Type} (T : S → S → Prop) : Nat → S → S → Prop
  | nil (s) : Walk T 0 s s
  | step {n s u v} : Walk T n s u → T u v → Walk T (n+1) s v

theorem closure_sound {S : Type} {T : S → S → Prop} {C : Set S}
    (closed : ∀ s ∈ C, ∀ u, T s u → u ∈ C)
    {n : Nat} {a b : S} (h : Walk T n a b) (ha : a ∈ C) : b ∈ C := by
  induction h with
  | nil => exact ha
  | step _ edge ih => exact closed _ (ih ha) _ edge

/-- Bond g appears 1+a times. The other bonds remain distinct. -/
def foldBond (g a i : Nat) := if i ≤ g then i else max g (i-a)

theorem clipped_tags (g a k i h : Nat) (left : h ≤ g)
    (right : g+h+2 ≤ k) (inside : i+2 ≤ k+a) :
    min i h = min (foldBond g a i) h ∧
    min (k+a-2-i) h = min (k-2-foldBond g a i) h := by
  unfold foldBond
  split <;> omega

/-- d=2+3q and both corner distances at least 308. -/
theorem ordinary_exit_cover (t q : Nat)
    (west : 308 ≤ 2+3*q) (east : 308+(2+3*q) ≤ 622+42*t) :
    ∃ q₀ a b : Nat, 102 ≤ q₀ ∧ q₀ ≤ 104 ∧ q=q₀+a ∧ a+b=14*t := by
  refine ⟨min q 104, q-min q 104, 14*t-(q-min q 104), ?_⟩
  omega

/-- Axis 2: a mobile central base, or an east-anchored base. -/
theorem axis_two_cover (k q : Nat) (large : 81 ≤ k) (inside : q+2 ≤ k)
    (late : 24 ≤ q) :
    (∃ a b : Nat, q=24+a ∧ k=81+a+b) ∨
    (∃ q₀ a : Nat, 25 ≤ q₀ ∧ q₀ ≤ 79 ∧ q=q₀+a ∧ k=81+a) := by
  by_cases h : q+57 ≤ k
  · exact Or.inl ⟨q-24,k-(q+57),by omega⟩
  · exact Or.inr ⟨q-(k-81),k-81,by omega⟩

end GridGraphs.FoldedStripCover
