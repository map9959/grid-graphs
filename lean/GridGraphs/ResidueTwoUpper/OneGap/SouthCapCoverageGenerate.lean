import GridGraphs.ResidueTwoUpper.OneGap.SouthCapCoverageProblem
import Std.Tactic.BVDecide.LRAT.Parser
import Lean.Meta.Tactic.BVDecide.LRAT.Trim

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open Std.Sat Std.Tactic.BVDecide

private def putVar (buf : ByteArray) (v : Nat) : ByteArray := Id.run do
  let mut b := buf
  let mut x := v
  for _ in [:10] do
    if x<128 then return b.push x.toUInt8
    b := b.push ((x%128)+128).toUInt8
    x := x/128
  return b

private def encode (buf : ByteArray) (bound : Nat) (proof : Array LRAT.IntAction) :
    IO ByteArray := do
  let mut adds := #[]
  let mut ids : Std.HashSet Nat := {}
  for action in proof do
    let (c,h) ← match action with
      | .del _ => continue
      | .addRat .. => throw (IO.userError "expected a RUP refutation")
      | .addRup _ c h => pure (c,h)
      | .addEmpty _ h => pure (#[],h)
    for i in h do
      if i≤bound then ids := ids.insert (i-1)
    adds := adds.push c
  let sorted := ids.toArray.qsort (·<·)
  let mut out := putVar buf sorted.size
  let mut prev := 0
  for i in sorted do
    out := putVar out (i-prev)
    prev := i
  out := putVar out adds.size
  for c in adds do
    out := putVar out c.size
    for v in c do out := putVar out (2*v.natAbs+(decide (v<0)).toNat)
  return out

/-- By default check both corner patterns at the last plaquette.
Pass `all` to produce the 98 refutations. Only trimmed RUP data is
retained, under `.lake`; the disposable LRAT trace is removed. -/
def generateCoverage (args : List String) : IO Unit := do
  let dir : System.FilePath := ".lake/south-cap-coverage"
  IO.FS.createDirAll dir
  let cnf := dir/"local.cnf"
  let lrat := dir/"local.lrat"
  let solver := (← IO.appDir)/"cadical"
  let tags := if args == ["all"] then List.range' 6 7 else [12]
  let mut data := ByteArray.empty
  for r in tags do
    for c in tags do
      for a in [false,true] do
        let f := coverageProblem r c a
        IO.FS.writeFile cnf f.dimacs
        try
          let res ← IO.Process.output {
            cmd := solver.toString
            args := #["--quiet","--lrat",cnf.toString,lrat.toString] }
          unless res.exitCode==20 do
            let literals := res.stdout.splitOn "\n" |>.filter (·.startsWith "v ")
            let pos := (literals.flatMap fun l => l.splitOn " " |>.filterMap String.toNat?).toArray
            let word := projectedWord (fun j => pos.contains (j+1))
            let masks := (List.range 4).map fun j => (word >>> (9*j))%512
            throw (IO.userError s!"({r},{c},{a}): CaDiCaL exit {res.exitCode}, {f.clauses.size} clauses, word {masks}")
          let proof ← IO.ofExcept (Lean.Meta.Tactic.BVDecide.LRAT.trim (← LRAT.loadLRATProof lrat))
          data ← encode data f.clauses.size proof
          IO.println s!"({r},{c},{a}): {f.clauses.size} clauses, {proof.size} trimmed actions"
        finally
          IO.FS.removeFile cnf
          if ← lrat.pathExists then IO.FS.removeFile lrat
  let out := dir/(if args == ["all"] then "all" else "pilot")
  IO.FS.writeBinFile out data
  let res ← IO.Process.output {cmd := "xz", args := #["-9","-f",out.toString]}
  unless res.exitCode==0 do throw (IO.userError res.stderr)
  IO.println s!"Trimmed certificate: {out}.xz ({data.size} bytes before compression)"

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap

def main := GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.generateCoverage
