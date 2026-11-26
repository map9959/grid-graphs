import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripBackward

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
namespace GridScan

abbrev Bank := Nat → Nat → List Word

def packedStep {h : Nat} (z : Update h) (j : Nat) (prev : Option Line)
    (line : Line) (state : PackedPartition) : Option PackedPartition :=
  let desc (old : Line) (i : Fin (3*z.window.depth)) :=
    lineMark z.window.axis (readLine old) 2 i
  (tileStep z.window.axis (replayTooth z.window z.north) (replayExits z.window) j
    (readLine line) (state,prev.map desc)).map Prod.fst

def startLayer {h : Nat} (z : Update h) (D : Bank) : List (Line × PackedPartition) :=
  (((pairTable z.window D 0).map Prod.fst).dedup.filterMap fun a =>
    (packedStep z 0 none a (Row.basePartition (3*z.window.depth)).pack).map (a,·)).dedup

def packedArcs {h : Nat} (z : Update h) (D : Bank) (j : Nat) : List (Arc Line PackedPartition) :=
  let tables := pairTable z.window D
  let step := fun j a b x => packedStep z (j+1) (some a) b x
  let F := layers tables step (startLayer z D)
  let last := z.window.length-1
  let live := backward tables step F (Row.Program.accepts (3*z.window.depth)) last (last-(j+1))
  backwardArcs tables step F live j

def acceptedWords {h : Nat} (z : Update h) (D : Bank) (j i : Nat) : List Word :=
  ((packedArcs z D j).map (fun arc => wordOf z.window.axis arc.1.1 arc.2.1 i)).dedup

private theorem tick_lastMarks {n : Nat} (tooth exits : Nat → Fin n → Bool)
    (j : Nat) (mark : Fin n → Bool) (old next : TileState n)
    (ok : tick tooth exits j mark old=some next) : next.2=some mark := by
  obtain ⟨x,_,hx⟩ := Option.bind_eq_some_iff.mp ok
  have eq : (x,some mark)=next := Option.some.inj hx
  rw [←eq]

theorem tileStep_lastMarks {n : Nat} (axis : Axis) (tooth exits : Nat → Fin n → Bool)
    (j : Nat) (line : Nat → Nat) (old next : TileState n)
    (ok : tileStep axis tooth exits j line old=some next) :
    next.2=some (fun i : Fin n => lineMark axis line 2 i) := by
  obtain ⟨a,_,ha⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨b,_,hb⟩ := Option.bind_eq_some_iff.mp ha
  exact tick_lastMarks _ _ _ _ b next hb

private theorem tileStep_readLine {n : Nat} (axis : Axis)
    (tooth exits : Nat → Fin (3*n) → Bool) (j : Nat) (line : Nat → Nat) (old : TileState (3*n)) :
    tileStep axis tooth exits j (readLine (lineOf line n 0)) old =
      tileStep axis tooth exits j line old := by
  have eq (phase : Nat) :
      (fun i : Fin (3*n) => lineMark axis (readLine (lineOf line n 0)) phase i) =
        (fun i : Fin (3*n) => lineMark axis line phase i) := by
    funext i
    have hi : i.val/3<n := by have := i.isLt; omega
    have read := lineOf_getD line n 0 (i.val/3) hi
    simp only [lineMark,readLine,read,Nat.zero_add]
  simp only [tileStep,eq]

/-- Every plaquette on a surviving packed trace occurs in the
executable forward/backward projection. This checks the direction
needed for domain deletion; no solver answer is trusted. -/
theorem acceptedWords_cover {h : Nat} (z : Update h) (D : Bank) (b : Tiles)
    (l : 2≤z.window.length)
    (consistent : z.window.Consistent (fun r c m => m∈D r c) b)
    (trace : z.window.HasTrace (tileSweep (3*z.window.depth) z.window.axis
      (replayTooth z.window z.north) (replayExits z.window)) b)
    (j i : Nat) (hj : j+2≤z.window.length) (hi : i+2≤z.window.depth) :
    acrossWord z.window.axis b j i∈acceptedWords z D j i := by
  obtain ⟨t,base,run,ok⟩ := trace
  let n := 3*z.window.depth
  let line := fun j => lineOf (b j) z.window.depth 0
  let state := fun j => (t (j+1)).1
  let tables := pairTable z.window D
  let step := fun j a b x => packedStep z (j+1) (some a) b x
  let last := z.window.length-1
  have accept : Row.Program.accepts n (state last)=true := by
    change Row.Program.accepts n (t z.window.length).1=true at ok
    simpa only [state,last,show z.window.length-1+1=z.window.length by omega] using ok
  have edges : ∀ k<last, (line k,line (k+1))∈tables k := by
    intro k hk
    exact pairTable_cover z.window D b k (by dsimp [last] at hk; omega) consistent
  have prev (k : Nat) (hk : k<z.window.length) :
      (t (k+1)).2=some (fun i : Fin n => lineMark z.window.axis (readLine (line k)) 2 i) := by
    have lastMarks := tileStep_lastMarks _ _ _ _ _ _ _
      (show tileStep z.window.axis (replayTooth z.window z.north) (replayExits z.window)
        k (b k) (t k)=some (t (k+1)) from run k hk)
    rw [lastMarks]
    congr 1
    funext i
    have il : i.val/3<z.window.depth := by have := i.isLt; dsimp [n] at *; omega
    simp only [line,lineMark,readLine,lineOf_getD _ _ _ _ il,Nat.zero_add]
  have init : (line 0,state 0)∈startLayer z D := by
    have inL : line 0∈((tables 0).map Prod.fst).dedup :=
      List.mem_dedup.mpr (List.mem_map.mpr ⟨_,edges 0 (by dsimp [last]; omega),rfl⟩)
    apply List.mem_dedup.mpr
    refine List.mem_filterMap.mpr ⟨line 0,inL,?_⟩
    unfold packedStep
    simp only [Option.map_map,Option.map_none,Function.comp_def]
    change (tileStep z.window.axis (replayTooth z.window z.north) (replayExits z.window)
      0 (readLine (line 0)) ((Row.basePartition n).pack,none)).map (fun s => (line 0,s.1))=_
    rw [show readLine (line 0)=readLine (lineOf (b 0) z.window.depth 0) from rfl,
      tileStep_readLine,←show t 0=((Row.basePartition n).pack,none) from base]
    exact congrArg (Option.map fun s : TileState n => (line 0,s.1)) (run 0 (by omega))
  have runs : ∀ k<last, step k (line k) (line (k+1)) (state k)=some (state (k+1)) := by
    intro k hk
    have kl : k+1<z.window.length := by dsimp [last] at hk; omega
    have eq : (state k,some (fun i : Fin n => lineMark z.window.axis (readLine (line k)) 2 i))=t (k+1) :=
      Prod.ext rfl (prev k (by omega)).symm
    change (tileStep z.window.axis (replayTooth z.window z.north) (replayExits z.window)
      (k+1) (readLine (lineOf (b (k+1)) z.window.depth 0))
      (state k,some (fun i : Fin n => lineMark z.window.axis (readLine (line k)) 2 i))).map Prod.fst=_
    rw [tileStep_readLine,eq]
    exact congrArg (Option.map Prod.fst) (run (k+1) kl)
  have jl : j<last := by dsimp [last]; omega
  have live := live_pair_cover last line state
    (layers_cover line state last init edges runs) edges runs accept j jl
  apply List.mem_dedup.mpr
  exact List.mem_map.mpr ⟨((line j,state j),(line (j+1),state (j+1))),live,wordOf_lines z.window b j i hi⟩

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
