import GridGraphs.ResidueTwoUpper.OneGap.ShortNorthGeo

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open L7 ResidueZero

/-- A 48-site window retains both complete width-dependent local
domains and the 16 aligned top seeds. Only the target tile is inspected. -/
def window (w : View) (v : Nat) (A : Board) : Board := build 48 fun r c =>
  let t := loc 25 v w r c
  let b := unview w 48 r c
  let xs := atRC A t.1 t.2
  if b.1=1 ∧ b.2%3=1 then xs.filter fun z => encode (Fin.ofNat 512 z.1) w==72 else xs
def target (w : View) (r c : Nat) := (if w.rowFar then 47-(if w.swap then c else r) else if w.swap then c else r,
    if w.colFar then 47-(if w.swap then r else c) else if w.swap then r else c)

@[noinline] def test (w : View) (v : Nat) (A : Board) :=
  let G := Kernel.prune 48 30 (window w v A)
  (List.range 4).all fun j => (List.range 4).all fun i =>
    let t := target w (3*(j+1)+1) (3*(i+12)+1)
    (atRC G t.1 t.2).all fun z => encode (Fin.ofNat 512 z.1) w==73
@[noinline] def allTests (A : Board) := decide (∀ w : View, ∀ j : Fin 4, test w (6+j.val) A)
theorem tests : allTests (cached 1 chart) := by native_decide
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
