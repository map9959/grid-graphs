import GridGraphs.ResidueTwoUpper.TwoGapCoverageRup
import GridGraphs.ResidueTwoUpper.TwoGapCoverageHandoff
import Lean

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
open Catalogue ExitReplay ResidueZero Stencil Words BoundarySix.Connected

-- Compression is outside the trust boundary. Only the bytes embedded
-- here reach the checker; invalid instructions cannot establish UNSAT.
open Lean Elab Term in
elab "include_rup_blob" : term => do
  let some dir := (System.FilePath.mk (← readThe Core.Context).fileName).parent
    | throwError "missing source directory"
  let child ← IO.Process.spawn {cmd := "xz", args := #["-dc", (dir / "Data/two_gap_coverage.xz").toString], stdout := .piped}
  let bytes ← child.stdout.readBinToEnd
  unless (← child.wait)==0 do throwError "cannot decompress coverage witness"
  -- Latin-1 gives a one-codepoint-per-byte Lean string literal.
  return mkStrLit (String.ofList (bytes.data.toList.map (fun b => Char.ofNat b.toNat)))

def bytecode : String := include_rup_blob
abbrev Reader := StateM Nat
def readVar (buf : ByteArray) : Reader Nat := do
  let mut n := 0
  for j in [:10] do
    let i ← get
    set (i+1)
    let x := (buf[i]?.getD 0).toNat
    n := n + ((x%128) <<< (7*j))
    if x<128 then return n
  return n
def decode (buf : ByteArray) : Reader (Array Nat × Learned) := do
  let mut ids := #[]
  let mut last := 0
  for _ in [:← readVar buf] do
    last := last+(← readVar buf)
    ids := ids.push last
  let mut clauses := #[]
  for _ in [:← readVar buf] do
    let mut cl := #[]
    for _ in [:← readVar buf] do cl := cl.push (← readVar buf)
    clauses := clauses.push cl
  return (ids,clauses)
def witnesses : List (Array Nat × Learned) :=
  let buf := ByteArray.mk <| bytecode.toList.toArray.map fun c => c.toNat.toUInt8
  ((List.range 14).mapM fun _ => decode buf).run' 0
def check (b : Nat) :=
  let cert := witnesses[b]!
  rupCheck (problem b) cert.1 cert.2

private theorem checked : ∀ b : Fin 14, check b := by native_decide
theorem local_to_catalogue : BaseCover := by
  intro c hc l L
  have bound : ∀ x ∈ allKeys, bucket x<14 := by native_decide
  exact common_sound hc L (rup_sound (checked ⟨bucket c,bound c hc⟩))

theorem physical_catalogue {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (canon : packed (signature (by omega) F)=code4 0 0 1 1) :
    ∃ P q s, North.Chart F P (2+3*q) ∧ Global F P s ∧
      (∀ i j : Int, four (pull s i j)=actual F i j) ∧
      3≤q ∧ q+4≤11+14*u ∧ ∀ j : Nat, j+1<11+14*u →
      permits tables[level (11+14*u) j]! (stripWord s q j) (stripWord s q ((j:Int)+1)) :=
  physical_of_baseCover local_to_catalogue F acy score two canon

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
