import Mathlib

namespace GridGraphs.SynchronousFront

/-- m slabs consume four rows each, transferring three columns of
the same physical width from the east padding to the western one. -/
theorem synchronized_sizes (k : Nat) (hk : 207 ≤ k) :
    ∃ m r : Nat, 20 ≤ r ∧ r ≤ 23 ∧ k = 28+4*m+r ∧
      (∀ j ≤ m, 81+3*j ≤ k) ∧
      (∀ j < m, 84+3*j ≤ k ∧ 28+4*j+13 < k-7) := by
  refine ⟨(k-48)/4, 20+(k-48)%4, ?_⟩
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · intro j hj; omega
  · intro j hj; constructor <;> omega

theorem move_padding (k m : Nat) (room : 84+3*m ≤ k) :
    -- The base step box has width 84 and these same additional
    -- insertions on both sides of the handoff.
    84+3*m+(k-84-3*m)=k ∧
    k-81-3*m=3+(k-84-3*m) ∧
    k-81-3*(m+1)=k-84-3*m := by omega

/-- Logical interface to the replayed seed, inductive strip and actual
southern boundary checks. No periodicity hypothesis on a filling. -/
theorem exclude (k : Nat) (hk : 207 ≤ k) (candidate : Prop)
    (inv : Nat → Prop)
    (seed : candidate → inv 0)
    (step : ∀ j, 84+3*j ≤ k → 28+4*j+13 < k-7 → candidate → inv j → inv (j+1))
    (tail : ∀ m r, 20 ≤ r → r ≤ 23 → k=28+4*m+r → 81+3*m ≤ k → candidate → ¬inv m) :
    ¬candidate := by
  intro c
  obtain ⟨m,r,hr,hr',size,pad,moves⟩ := synchronized_sizes k hk
  have go : ∀ j ≤ m, inv j := by
    intro j
    induction j with
    | zero => exact fun _ => seed c
    | succ j ih =>
      intro h
      obtain ⟨a,b⟩ := moves j (by omega)
      exact step j a b c (ih (by omega))
  exact tail m r hr hr' size (pad m (by omega)) c (go m (by omega))

/-- The shrinking even fan reaches a terminal rectangle above the south fringe. -/
theorem even_fan_sizes (k q : Nat) (hk : 207 ≤ k) (hq : 58 ≤ q)
    (hpos : q+2 ≤ k) (he : q%2=0) :
    ∃ m, (q-44-6*m=14 ∨ q-44-6*m=16 ∨ q-44-6*m=18) ∧
      (∀ j < m, 20 ≤ q-44-6*j) ∧ 7+m+13 < k-7 := by
  refine ⟨(q-58)/6, ?_, ?_, ?_⟩
  · omega
  · intro j hj; omega
  · omega

/-- Room at every dangling-line handoff and after switching to the
rooted rate. All variables are coordinates of the *same* square. -/
theorem odd_speed_room (k q y c m : Int) (hk : k ≥ 2000)
    (hpos : q+2 ≤ k) (fan : q=6*y+c+2) (hc : 13 ≤ c ∧ c ≤ 17)
    (height : y+6+13*m+31 ≤ k) :
    let f := q-3*y+3+7*m
    f+64 ≤ k ∧ (f+17>q ∨ f+17>k-8 →
       ∀ l : Int, y+6+13*m+4*l+31 ≤ k → q+1+3*l+64 ≤ k) := by
  dsimp
  constructor
  · omega
  · intro stop l height'; omega

end GridGraphs.SynchronousFront
