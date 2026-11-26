import GridGraphs.NoPitch.StarCoverage
import GridGraphs.Tests.FaceDualReplay

namespace GridGraphs.NoPitch.Dual
open PitchCut

/-- The chart's *actual* column weights times their multiplicities,
and completeness of its occupied star dictionary at these widths. -/
theorem column19 : unitCheck chart19 && covers chart19 6 := by native_decide
theorem column22 : unitCheck chart22 && covers chart22 7 := by native_decide
theorem column25 : unitCheck chart25 && covers chart25 8 := by native_decide
theorem column52 : unitCheck chart52 && covers chart52 17 := by native_decide
theorem column58 : unitCheck chart58 && covers chart58 19 := by native_decide
theorem column61 : unitCheck chart61 && covers chart61 20 := by native_decide

inductive Width | n19 | n22 | n25 | n52 | n58 | n61
deriving DecidableEq, Repr
def Width.k : Width → Nat
  | .n19 => 6 | .n22 => 7 | .n25 => 8 | .n52 => 17 | .n58 => 19 | .n61 => 20
def Width.chart : Width → Chart
  | .n19 => chart19 | .n22 => chart22 | .n25 => chart25
  | .n52 => chart52 | .n58 => chart58 | .n61 => chart61

def roundTrip (D : Chart) :=
  let m := index D
  decide (∀ j : Fin D.cols.size, locate D m D.cols[j].key=some j)

theorem dictionaries (w : Width) : roundTrip w.chart && w.chart.cols.all (fun c => 0<c.units) := by
  cases w <;> native_decide

theorem width_objective (w : Width) (F : Finset (Site w.k))
    (acy : (forcedEdgeGraph (gridGraph (N w.k) (N w.k)) (↑F : Set _)).IsAcyclic)
    (out : Site w.k → Option (Fin 4)) (inside : ∀ x d, d∈out x → (Keys.probe x d.val).isSome) :
    score w.chart (physicalVector w.chart F out)=8*(F.card:Int) := by
  have ok : unitCheck w.chart && covers w.chart w.k := by
    cases w
    exacts [column19,column22,column25,column52,column58,column61]
  obtain ⟨units,cover⟩ := Bool.and_eq_true_iff.mp ok
  exact vector_objective units (Bool.and_eq_true_iff.mp (dictionaries w)).2 cover F acy out inside

theorem physical_finite_upper (w : Width) (small : w.k<19) (F : Finset (Site w.k))
    (acy : (forcedEdgeGraph (gridGraph (N w.k) (N w.k)) (↑F : Set _)).IsAcyclic)
    (out : Site w.k → Option (Fin 4)) (inside : ∀ x d, d∈out x → (Keys.probe x d.val).isSome)
    (physical : Feasible w.chart (physicalVector w.chart F out) 8 0 (8*(N w.k:Int)^2)) :
    F.card ≤ squareScore (N w.k) := by
  have check : finiteCheck w.chart (N w.k) := by
    cases w
    exacts [verified19,verified22,verified25,verified52,
      False.elim ((by decide : ¬ Width.n58.k<19) small),
      False.elim ((by decide : ¬ Width.n61.k<19) small)]
  exact finite_bound _ check physical (width_objective w F acy out inside)

end GridGraphs.NoPitch.Dual
