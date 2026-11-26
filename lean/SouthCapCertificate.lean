import GridGraphs.ResidueTwoUpper.OneGap.SouthCapCoverageProblem
import GridGraphs.ResidueTwoUpper.TwoGapCoverageRup

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage

open Lean Elab Term in
elab "include_south_cap_refutations" : term => do
  let some dir := (System.FilePath.mk (← readThe Core.Context).fileName).parent
    | throwError "missing source directory"
  let path := dir / "GridGraphs" / "ResidueTwoUpper" / "OneGap" / "SouthCapCoverageAll.xz"
  let child ← IO.Process.spawn {cmd := "xz", args := #["-dc",path.toString], stdout := .piped}
  let bytes ← child.stdout.readBinToEnd
  unless (← child.wait)==0 do throwError "cannot decompress southern coverage witnesses"
  return mkStrLit (witnessLiteral bytes)

private def data : String := include_south_cap_refutations
private def witness : Array (Array Nat × Learned) :=
  let buf := witnessBytes data
  ((List.range 98).mapM fun _ => Witness.decode buf).run' 0 |>.toArray

-- The two frames differ only where the window reaches a switched site.
private def varies (r c : Nat) : Bool := sites.any fun p =>
  seFrame false (absAt r c p) != seFrame true (absAt r c p)

private theorem sameProblem {r c} (h : varies r c=false) :
    coverageProblem r c false=coverageProblem r c true := by
  have eq : ∀ p∈sites, seFrame false (absAt r c p)=seFrame true (absAt r c p) := by
    simpa [varies,List.any_eq_false] using h
  suffices rows : clauseRows r c false=clauseRows r c true by simp [coverageProblem,rows]
  apply List.flatMap_congr
  intro p hp
  dsimp only
  rw [eq p hp]

private def testCase (w : Array (Array Nat × Learned)) (r c : Fin 7) (a : Bool) :=
  let t := w[14*r.val+2*c.val+a.toNat]!
  rupCheck (coverageProblem (6+r.val) (6+c.val) a) t.1 t.2

@[noinline] private def allCheck (w : Array (Array Nat × Learned)) (r : Fin 7) : Bool :=
  decide (∀ c : Fin 7, testCase w r c false ∧
    (varies (6+r.val) (6+c.val)=true → testCase w r c true=true))

-- Materialize the tasks before joining them. Rows share the same
-- decoded witness array; each row builds just one CNF at a time.
@[noinline] private def jobs (w : Array (Array Nat × Learned)) :=
  (List.finRange 7).map fun r => Task.spawn fun _ => allCheck w r

private def parallelCheck (w : Array (Array Nat × Learned)) :=
  (jobs w).all fun job => job.get

set_option maxHeartbeats 0 in
private theorem replayed : parallelCheck witness := by native_decide

private theorem checked (r : Fin 7) : allCheck witness r := by
  exact List.all_eq_true.mp replayed _ (List.mem_map_of_mem (f:=fun z => Task.spawn fun _ =>
    allCheck witness z) (List.mem_finRange r))

theorem all_windows_coverage (r c : Fin 7) (a : Bool) (assign : Nat → Bool)
    (physical : ∀ cl∈clauseRows (6+r.val) (6+c.val) a, cl.eval assign=true) :
    ∃ m∈allowedWords (6+r.val) (6+c.val), ∀ z∈fourVars.zipIdx, assign z.1=m.testBit z.2 :=
  by
    have checks := of_decide_eq_true (checked r) c
    apply admitted_bits _ assign physical
    cases a with
    | false => exact rup_sound checks.1
    | true =>
      cases h : varies (6+r.val) (6+c.val) with
      | false => rw [←sameProblem h]; exact rup_sound checks.1
      | true => exact rup_sound (checks.2 h)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
