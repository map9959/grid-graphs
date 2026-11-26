import GridGraphs.Constructions.ResidueTwo.LowerTurnTable

/-! Developer diagnostic: identifies the first failing local implication
and coordinate residue for a requested base. It is not part of the proof. -/
open GridGraphs.ResidueTwoLower GridGraphs.ResidueTwoLower.Poly

def main (args : List String) : IO UInt32 := do
  for raw in args do
    let some b := raw.toNat? | return 2
    let c := charts b
    for s in [:c.size] do
      for d in dirs do
        for (e,same) in [(d,true),(Turn.turnL d,false),(Turn.turnR d,false)] do
          let q := trial c s d e same
          let some pitch := candidates.find? (fun p => q.all fun a => (a.lower p 0 0 0).isSome)
            | IO.println s!"base {b}, layer {s}, {repr d} -> {repr e}: unsupported divisor"; return 1
          for t in [:pitch.t] do
            for i in [:pitch.i] do
              for j in [:pitch.j] do
                unless checkResidue pitch q t i j do
                  IO.println s!"base {b}, layer {s}, {repr d} -> {repr e}: residue {t},{i},{j}"
                  return 1
      IO.println s!"base {b}, layer {s}: pass"
  return 0
