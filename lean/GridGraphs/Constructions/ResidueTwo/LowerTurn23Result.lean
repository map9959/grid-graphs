import GridGraphs.Constructions.ResidueTwo.LowerTurnBase23Cover
import GridGraphs.Results.ResidueTwoLower

namespace GridGraphs.ResidueTwoLower.Poly

/-- The physical mask inclusion is unconditional at this progression: no
route hypothesis or mask-cardinality proof is needed by the caller. -/
theorem base23_lower_of_layers (layers : chartOK input23 = true) (t : Nat) :
    squareScore (23+42*t) ≤ maxPreserved (23+42*t) (23+42*t) := by
  let k := 7+14*t
  have n : 3*k+2=23+42*t := by dsimp [k]; omega
  by_cases small : k≤38
  · simpa only [n] using squareScore_lower_through_116 k small
  have routes := routes_of_chart (marks (23+42*t)) (by decide +native : input23.size>0)
    layers (forced23 t)
  let G := holeDual (23+42*t) (marks (23+42*t))
  have path (x : GridFace (23+42*t) (23+42*t)) : G.Reachable x .out := by
    cases x with
    | out => exact .refl _
    | cell r c => exact routes r c
  let : Nonempty (GridFace (23+42*t) (23+42*t)) := ⟨.out⟩
  have con : G.Connected := ⟨fun a b => (path a).trans (path b).symm⟩
  have sz := marks_card_eq_squareScore k (by omega)
  dsimp only at sz
  rw [n] at sz
  rw [←sz]
  let U := Finset.univ.filter (fun v : GridVertex (23+42*t) (23+42*t) =>
    marks (23+42*t) v.1 v.2 = false)
  have complement : Finset.univ \ U = Finset.univ.filter (fun v : GridVertex (23+42*t) (23+42*t) =>
    marks (23+42*t) v.1 v.2) := by ext; simp [U]
  rw [←complement]
  exact compl_card_le_maxPreserved_of_uuDual_connected (by omega) (by omega) U con

end GridGraphs.ResidueTwoLower.Poly
