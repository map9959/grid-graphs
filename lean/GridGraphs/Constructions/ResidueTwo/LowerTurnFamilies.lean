import GridGraphs.Constructions.ResidueTwo.LowerTurnAltTail
import GridGraphs.Results.ResidueTwoLower

namespace GridGraphs.ResidueTwoLower.Poly

def baseOf (k : Nat) : Nat :=
  match k%14 with
  | 0 => 44 | 1 => 47 | 2 => 50 | 3 => 53 | 4 => 56 | 5 => 59 | 6 => 62
  | 7 => 23 | 8 => 68 | 9 => 71 | 10 => 74 | 11 => 35 | 12 => 38 | _ => 41

def baseList : List Nat := [23,35,38,41,44,47,50,53,56,59,62,68,71,74]

private theorem phaseOf (k : Nat) (hk : 39≤k) :
    baseOf k ∈ baseList ∧ baseOf k+42*((3*k+2-baseOf k)/42)=3*k+2 := by
  have hr := Nat.mod_lt k (by decide : 0<14)
  interval_cases h : k%14 <;> simp [baseOf,baseList,h] <;> omega

def physRegion (b : Nat) :=
  if b=56 then altRegion else if b=23 ∨ b=35 ∨ b=41 ∨ b=59 then ordinaryRegion b
    else repairedRegion b

theorem physical_covers (b t : Nat) (hb : b∈baseList) (i j : Nat)
    (hi : i<b+42*t) (hj : j<b+42*t) (h : marks (b+42*t) i j=true) :
    (physRegion b).eval t i j := by
  unfold physRegion
  split <;> rename_i alt
  · subst b; exact alternating_covers _ _ _ hi hj h
  split <;> rename_i ord
  · exact ordinary_covers _ _ _ _ ord hi hj h
  · apply repaired_covers _ _ _ _ _ hi hj h
    simp [baseList] at hb; unfold repairedBase; omega

/-- The fourteen Boolean checks, applied to the physical mark regions, give
the direct zipper-routes premise of the all-residue assembly. -/
theorem zipper_routes_of_chart_table (charts : Nat → Chart)
    (bounds : ∀ b ∈ baseList, 0<(charts b).size ∧ chartOK (charts b)=true ∧
      coverOK (charts b) (widthExpr b) (physRegion b)=true)
    (k : Nat) (hk : 39≤k) :
    let n := 3*k+2
    ∀ r c : Fin (n-1), (holeDual n (marks n)).Reachable (.cell r c) .out := by
  let b := baseOf k
  let t := (3*k+2-b)/42
  obtain ⟨inList,side⟩ := phaseOf k hk
  change b+42*t=3*k+2 at side
  rw [←side]
  obtain ⟨pos,ok,co⟩ := bounds b inList
  apply routes_of_chart (t := t) _ pos ok
  apply cover_sound _ _ (physical_covers b t inList) co
  intro i j
  simp [widthExpr,Exp.eval]

theorem lower_of_chart_table (charts : Nat → Chart)
    (bounds : ∀ b ∈ baseList, 0<(charts b).size ∧ chartOK (charts b)=true ∧
      coverOK (charts b) (widthExpr b) (physRegion b)=true)
    (k : Nat) : squareScore (3*k+2) ≤ maxPreserved (3*k+2) (3*k+2) :=
  squareScore_lower_of_zipper_routes (zipper_routes_of_chart_table charts bounds) k

end GridGraphs.ResidueTwoLower.Poly
