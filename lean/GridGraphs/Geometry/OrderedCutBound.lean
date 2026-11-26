import Mathlib

namespace GridGraphs.OrderedCutBound

/-- Arithmetic interface to the ordered cut transfer. An empty cost set
stays empty; every cost translates by the same amount after 42 tiles. -/
theorem no_budget (accepts : Nat → Nat → Prop)
    (base : ∀ d, accepts 0 d → d = 234)
    (one : ∀ d, ¬ accepts 1 d) (two : ∀ d, ¬ accepts 2 d)
    (cycle : ∀ t d, accepts (t+3) d → ∃ c, accepts t c ∧ d=c+252)
    (t : Nat) : ¬ accepts t (198+72*t) := by
  have aux : ∀ n d, accepts n d → d = 234+84*n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hd
      rcases n with _|(_|(_|m))
      · exact base d hd
      · exact False.elim (one d hd)
      · exact False.elim (two d hd)
      · obtain ⟨c,hc,eq⟩ := cycle m d hd
        rw [eq, ih m (by omega) c hc]
        change 234+84*m+252 = 234+84*(m+3)
        ring
  intro hd
  have := aux t _ hd
  omega

/-- Physical north-to-south coordinates cannot advance four edges per
bulk column for the whole required interval at t >= 2. -/
theorem drift_bound (t y₀ y₁ : Nat)
    (moves : y₀ + 4*(25+14*t) = y₁)
    (on_board : y₁ < 3*(39+14*t)) : t ≤ 1 := by omega

/-- Three ordered hops admit a second terminal class, but it too starts
above budget. Over the verified period the gap increases by 36. -/
theorem three_port_gap (accepts : Nat → Nat → Prop)
    (base : ∀ d, accepts 0 d → d = 234)
    (one : ∀ d, accepts 1 d → d = 324) (two : ∀ d, ¬ accepts 2 d)
    (cycle : ∀ t d, accepts (t+3) d → ∃ c, accepts t c ∧ d=c+252)
    (t d : Nat) (hd : accepts t d) : 198+72*t+36 ≤ d := by
  induction t using Nat.strong_induction_on generalizing d with
  | h n ih =>
    rcases n with _|(_|(_|m))
    · rw [base d hd]
    · rw [one d hd]; decide
    · exact False.elim (two d hd)
    · obtain ⟨c,hc,eq⟩ := cycle m d hd
      have h := ih m (by omega) c hc
      change 198+72*(m+3)+36 ≤ d
      omega

/-- The accepting path visits both insertion interfaces. Inserting closed
walks there keeps them available for subsequent insertions. The predicate
describes interface paths, not spanning trees. -/
theorem pump_budget (anchored : Nat → Nat → Prop) (h : Nat) (pos : 0 < h)
    (base : ∀ t < h, anchored t (198+72*t))
    (pump : ∀ t d, anchored t d → anchored (t+h) (d+72*h)) :
    ∀ t, anchored t (198+72*t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases b : t < h
    · exact base t b
    · have ht : t-h+h=t := by omega
      have a := pump (t-h) _ (ih (t-h) (by omega))
      rw [ht] at a
      convert a using 1
      omega

/-- Arithmetic of the absolute-row fan. Realizability of its column
words is separate; the fixed-height replay verifies it at side 623. -/
theorem fan_arithmetic (t : Nat) :
    let k := 39+14*t
    let q := 19+4*t
    let y := 13+2*t
    3*(q-4)+2*7+3*9+6*(k-q-2)+4 = 198+72*t ∧
      y+25+4*(k-2-q) = 3*k-7 := by
  dsimp
  omega

end GridGraphs.OrderedCutBound
