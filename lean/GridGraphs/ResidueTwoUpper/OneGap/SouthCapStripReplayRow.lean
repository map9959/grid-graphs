import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayExec

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip

/-- Store the result of each merge instead of keeping nested closures.
In particular, subsequent reads don't repeat all earlier merges. -/
private def Partition.tabulate {n : Nat} (p : Partition n) : Partition n :=
  let labels := Array.ofFn p.label
  let marks := Array.ofFn p.marked
  let opens := Array.ofFn p.opened
  ⟨fun i => labels[i.val]'(by simpa only [labels,Array.size_ofFn] using i.isLt),
   fun i => marks[i.val]'(by simpa only [marks,Array.size_ofFn] using i.isLt),
   fun i => opens[i.val]'(by simpa only [opens,Array.size_ofFn] using i.isLt)⟩

private theorem Partition.tabulate_eq {n : Nat} (p : Partition n) : p.tabulate=p := by
  cases p
  simp only [Partition.tabulate,Array.getElem_ofFn,Fin.eta]

private def insertEdgesTab {n : Nat} (p : Partition n) : List (SlotEdge n) → Option (Partition n)
  | [] => some p
  | (a,b)::es => (p.insert a b).bind (fun next => insertEdgesTab next.tabulate es)

private theorem insertEdgesTab_eq {n : Nat} (p : Partition n) (es : List (SlotEdge n)) :
    insertEdgesTab p es=insertEdges p es := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    cases e
    simp only [insertEdgesTab,insertEdges,Partition.tabulate_eq,ih]

namespace GridScan

private def tickTab {n : Nat} (tooth exits : Nat → Fin n → Bool) (j : Nat)
    (mark : Fin n → Bool) (old : TileState n) : Option (TileState n) := do
  let p ← insertEdgesTab (Row.extend (Partition.unpack (n+1) old.1) mark (exits j))
    (Row.edges old.2 mark (tooth j))
  let t ← closeRow p (Row.drop n) Row.keep
  return (t,some mark)

private theorem tickTab_eq {n : Nat} (tooth exits : Nat → Fin n → Bool) (j : Nat)
    (mark : Fin n → Bool) (old : TileState n) :
    tickTab tooth exits j mark old=tick tooth exits j mark old := by
  simp only [tickTab,tick,Row.transition,rowCore,insertEdgesTab_eq]
  cases insertEdges (Row.extend (Partition.unpack (n+1) old.1) mark (exits j))
    (Row.edges old.2 mark (tooth j)) <;> rfl

private def tileStepTab {n : Nat} (axis : Axis) (tooth exits : Nat → Fin n → Bool)
    (j : Nat) (line : Nat → Nat) (old : TileState n) : Option (TileState n) := do
  let x ← tickTab tooth exits (3*j) (fun i => lineMark axis line 0 i) old
  let y ← tickTab tooth exits (3*j+1) (fun i => lineMark axis line 1 i) x
  tickTab tooth exits (3*j+2) (fun i => lineMark axis line 2 i) y

private theorem tileStepTab_eq {n : Nat} (axis : Axis) (tooth exits : Nat → Fin n → Bool)
    (j : Nat) (line : Nat → Nat) (old : TileState n) :
    tileStepTab axis tooth exits j line old=tileStep axis tooth exits j line old := by
  simp only [tileStepTab,tileStep,tickTab_eq]

def packedStepTab {h : Nat} (z : Update h) (j : Nat) (prev : Option Line)
    (line : Line) (state : PackedPartition) : Option PackedPartition :=
  let desc (old : Line) (i : Fin (3*z.window.depth)) :=
    lineMark z.window.axis (readLine old) 2 i
  (tileStepTab z.window.axis (replayTooth z.window z.north) (replayExits z.window) j
    (readLine line) (state,prev.map desc)).map Prod.fst

theorem packedStepTab_eq {h : Nat} (z : Update h) (j : Nat) (prev : Option Line)
    (line : Line) (state : PackedPartition) :
    packedStepTab z j prev line state=packedStep z j prev line state := by
  simp only [packedStepTab,packedStep,tileStepTab_eq]

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
