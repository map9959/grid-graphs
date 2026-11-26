import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPhysicalStar
import GridGraphs.ResidueTwoUpper.TwoGapCoverageCert

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
open ResidueZero Stencil

-- Decompression only supplies bytes. The proved RUP checker still
-- verifies every refutation against the Lean-defined CNF.
open Lean Elab Term in
elab "include_south_cap_pilot" : term => do
  let some dir := (System.FilePath.mk (← readThe Core.Context).fileName).parent
    | throwError "missing source directory"
  let path := dir / ".." / "ResidueTwoUpper" / "OneGap" / "SouthCapCoveragePilot.xz"
  let child ← IO.Process.spawn {cmd := "xz", args := #["-dc",path.toString], stdout := .piped}
  let bytes ← child.stdout.readBinToEnd
  unless (← child.wait)==0 do throwError "cannot decompress southern coverage pilot"
  return mkStrLit (String.ofList (bytes.data.toList.map (fun b => Char.ofNat b.toNat)))

private def data : String := include_south_cap_pilot
private def witness : Array (Array Nat × Learned) :=
  let buf := ByteArray.mk (data.toList.toArray.map fun c => c.toNat.toUInt8)
  ((List.range 2).mapM fun _ => decode buf).run' 0 |>.toArray

private theorem checked (a : Bool) :
    rupCheck (coverageProblem 12 12 a) witness[a.toNat]!.1 witness[a.toNat]!.2 := by
  cases a <;> native_decide

theorem southeast_window_coverage (a : Bool) (assign : Nat → Bool)
    (physical : ∀ cl∈clauseRows 12 12 a, cl.eval assign=true) :
    ∃ m∈allowedWords 12 12, ∀ z∈fourVars.zipIdx, assign z.1=m.testBit z.2 :=
  admitted_bits (rup_sound (checked a)) assign physical

/-- The southeast replay applies to the projected physical halo:
rim, patch and star premises are all supplied by the scored forest. -/
theorem southeast_physical_bits {u k h w r c F v q} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q (fanDirection u v))
    (row : endTag h r=12) (col : endTag w c=12)
    (acy : (Bonds F).IsAcyclic)
    (score : F.card=440+1020*u+588*u^2) :
    ∃ m∈allowedWords 12 12, ∀ z∈fourVars.zipIdx,
      numericField (windowField pl H) z.1=m.testBit z.2 := by
  apply southeast_window_coverage H.cornerBit
  simpa only [row,col] using scored_halo_clauses pl H acy score

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
