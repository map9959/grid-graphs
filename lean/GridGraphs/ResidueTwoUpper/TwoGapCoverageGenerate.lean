import GridGraphs.ResidueTwoUpper.TwoGapCoverageCommon
import Std.Tactic.BVDecide.LRAT.Parser
import Lean.Meta.Tactic.BVDecide.LRAT.Trim

/-! Reproduce the local certificate from the Lean formula. Run in `lean/`
with `LEAN_NUM_THREADS=1 lake env lean --run GridGraphs/ResidueTwoUpper/TwoGapCoverageGenerate.lean`.
Only one local problem and its disposable LRAT proof exist at a time. -/
open GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage Std.Tactic.BVDecide
namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage.Generate

private def varint (dst : ByteArray) (v : Nat) : ByteArray := Id.run do
  let mut r := dst
  let mut x := v
  for _ in [:10] do
    if x<128 then return r.push x.toUInt8
    r := r.push ((x%128)+128).toUInt8
    x := x/128
  return r

def encode (data : ByteArray) (bound : Nat) (proof : Array LRAT.IntAction) : IO ByteArray := do
  let mut adds := #[]
  let mut ids : Std.HashSet Nat := {}
  for action in proof do
    let (c,h) ← match action with
      | .del _ => continue
      | .addRat .. => throw (IO.userError "expected RUP")
      | .addRup _ c h => pure (c,h)
      | .addEmpty _ h => pure (#[],h)
    for i in h do
      if i≤bound then ids := ids.insert (i-1)
    adds := adds.push c
  let sorted := ids.toArray.qsort (·<·)
  let mut out := varint data sorted.size
  let mut prev := 0
  for i in sorted do
    out := varint out (i-prev)
    prev := i
  out := varint out adds.size
  for c in adds do
    out := varint out c.size
    for v in c do out := varint out (2*v.natAbs+(decide (v<0)).toNat)
  return out

def run : IO Unit := do
  let dir : System.FilePath := ".lake/two-gap-coverage"
  IO.FS.createDirAll dir
  let dimacs := dir/"local.cnf"
  let trace := dir/"local.lrat"
  let solver := (← IO.appDir)/"cadical"
  let mut data := ByteArray.empty
  for b in [:14] do
    let f := problem b
    IO.FS.writeFile dimacs f.dimacs
    try
      let res ← IO.Process.output {cmd := solver.toString, args := #["--quiet","--lrat",dimacs.toString,trace.toString]}
      unless res.exitCode==20 do throw (IO.userError s!"bucket {b}: solver returned {res.exitCode}")
      let proof ← IO.ofExcept (Lean.Meta.Tactic.BVDecide.LRAT.trim (← LRAT.loadLRATProof trace))
      data ← encode data f.clauses.size proof
    finally
      IO.FS.removeFile dimacs
      if ← trace.pathExists then IO.FS.removeFile trace
  let blob := dir/"coverage"
  IO.FS.writeBinFile blob data
  let res ← IO.Process.output {cmd := "xz", args := #["-9","-f",blob.toString]}
  unless res.exitCode==0 do throw (IO.userError res.stderr)
  IO.println s!"certificate: {blob}.xz"

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage.Generate
def main := GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage.Generate.run
