import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplaySchedule
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayIndex
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayRow

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan

deriving instance Hashable for PackedPartition

private def scan {α : Type} (base : α) (step : Nat → α → α) : Nat → Array α
  | 0 => #[base]
  | k+1 =>
    let a := scan base step k
    a.push (step k (a[k]?.getD base))

private theorem scan_size {α : Type} (base : α) (step : Nat → α → α) (k : Nat) :
    (scan base step k).size=k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [scan,ih]

private theorem scan_read {α : Type} (base : α) (step : Nat → α → α) (f : Nat → α)
    (zero : f 0=base) (next : ∀ j, f (j+1)=step j (f j)) (k j : Nat) (hj : j≤k) :
    ((scan base step k)[j]?).getD base=f j := by
  induction k generalizing j with
  | zero =>
    have e : j=0 := by omega
    subst j
    exact zero.symm
  | succ k ih =>
    rw [scan,Array.getElem?_push,scan_size]
    split
    · rename_i eq
      subst j
      rw [Option.getD_some,ih k le_rfl,←next]
    · exact ih j (by omega)

private def startLayerTab {h : Nat} (z : Update h) (D : Bank) : List (Line × PackedPartition) :=
  indexedDedup ((indexedDedup ((pairTable z.window D 0).map Prod.fst)).filterMap fun a =>
    (packedStepTab z 0 none a (Row.basePartition (3*z.window.depth)).pack).map (a,·))

private theorem startLayerTab_eq {h : Nat} (z : Update h) (D : Bank) :
    startLayerTab z D=startLayer z D := by
  simp only [startLayerTab,startLayer,indexedDedup_eq,packedStepTab_eq]

/-- Compute each forward layer and backward layer once for this strip.
The original evaluator recomputes both for each requested plaquette. -/
@[noinline] def cachedArcTable {h : Nat} (z : Update h) (D : Bank) :
    Array (List (Arc Line PackedPartition)) :=
  let last := z.window.length-1
  let table := Array.ofFn (n := last) fun j => pairTable z.window D j.val
  let tables := fun j : Nat => table[j]?.getD []
  let step := fun j a b x => packedStepTab z (j+1) (some a) b x
  let base := startLayerTab z D
  let forward := scan base (fun j live => indexedDedup (indexedStep (tables j) (step j) live)) last
  let F := fun j : Nat => forward[j]?.getD base
  let endStates := (F last).filter (fun a => Row.Program.accepts (3*z.window.depth) a.2)
  let back := scan endStates (fun k live =>
    indexedDedup ((indexedLayerArcs tables step F live (last-(k+1))).map Prod.fst)) last
  Array.ofFn (n := last) fun j =>
    indexedLayerArcs tables step F (back[last-(j.val+1)]?.getD endStates) j.val

def arcWords (axis : Axis) (arcs : Array (List (Arc Line PackedPartition))) (j i : Nat) : List Word :=
  indexedDedup ((arcs[j]?.getD []).map (fun a => wordOf axis a.1.1 a.2.1 i))

def cachedSupports {h : Nat} (z : Update h) (D : Bank) : Nat → Nat → List Word :=
  arcWords z.window.axis (cachedArcTable z D)

private theorem cachedSupports_eq {h : Nat} (z : Update h) (D : Bank) (j i : Nat)
    (hj : j+2 ≤ z.window.length) :
    cachedSupports z D j i=acceptedWords z D j i := by
  let last := z.window.length-1
  let table := Array.ofFn (n := last) fun j => pairTable z.window D j.val
  let tables := fun j : Nat => table[j]?.getD []
  let step := fun j a b x => packedStep z (j+1) (some a) b x
  let base := startLayer z D
  let fstep := fun j live => (forwardStep (tables j) (step j) live).dedup
  let F := fun j : Nat => (scan base fstep last)[j]?.getD base
  let accept := Row.Program.accepts (3*z.window.depth)
  let endStates := (F last).filter (fun a => accept a.2)
  let bstep := fun k live =>
    ((backwardArcs tables step F live (last-(k+1))).map Prod.fst).dedup
  have tab (k : Nat) (hk : k<last) : tables k=pairTable z.window D k := by
    simp [tables,table,Array.getElem?_ofFn,hk]
  have front (k : Nat) (hk : k≤last) :
      F k=layers (pairTable z.window D) step base k := by
    rw [show F k=(layers tables step base k) from
      scan_read base fstep (layers tables step base) rfl (fun _ => rfl) last k hk]
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [layers,layers,tab k (by omega),ih (by omega)]
  have arcsEq (k : Nat) (hk : k<last) (live : List (Line × PackedPartition)) :
      backwardArcs tables step F live k =
        backwardArcs (pairTable z.window D) step (layers (pairTable z.window D) step base) live k := by
    simp only [backwardArcs,tab k hk,front k (by omega)]
  have back (k : Nat) (hk : k≤last) :
      ((scan endStates bstep last)[k]?).getD endStates =
        backward (pairTable z.window D) step (layers (pairTable z.window D) step base) accept last k := by
    let b := backward tables step F accept last
    rw [scan_read endStates bstep b rfl (fun _ => rfl) last k hk]
    change b k=_
    induction k with
    | zero => simp only [b,backward,front last le_rfl]
    | succ k ih =>
      simp only [b,backward]
      rw [arcsEq _ (by omega)]
      have prev := ih (by omega)
      dsimp only [b] at prev
      rw [prev]
  have jl : j<last := by dsimp [last]; omega
  simp only [cachedSupports,arcWords,cachedArcTable,acceptedWords,packedArcs,indexedDedup_eq,indexedStep_eq,
    indexedLayerArcs_eq,packedStepTab_eq,startLayerTab_eq]
  rw [Array.getElem?_ofFn,dif_pos (show j<z.window.length-1 from jl),Option.getD_some]
  change ((backwardArcs tables step F
    ((scan endStates bstep last)[last-(j+1)]?.getD endStates) j).map
      (fun a => wordOf z.window.axis a.1.1 a.2.1 i)).dedup=_
  rw [back _ (by omega),arcsEq j jl]

def cachedUpdate {h : Nat} (z : Update h) (D : Bank) : Bank :=
  let supports := cachedSupports z D
  fun r c => match localCell z.window r c with
  | none => D r c
  | some (j,i) => supports j i

theorem cachedUpdate_eq {h : Nat} (z : Update h) (D : Bank) :
    cachedUpdate z D=updateBank z D := by
  funext r c
  unfold cachedUpdate updateBank
  cases hit : localCell z.window r c with
  | none => rfl
  | some p =>
    obtain ⟨j,i⟩ := p
    exact cachedSupports_eq z D j i ((localCell_spec z.window r c j i).mp hit).1

def cachedExecute {h : Nat} : List (Update h) → Bank → Bool
  | [],D => (emptyCell h D).isSome
  | z::zs,D =>
    if (emptyCell h D).isSome then true
    else cachedExecute zs (materialize h (cachedUpdate z D))

theorem cachedExecute_eq {h : Nat} (zs : List (Update h)) (D : Bank) :
    cachedExecute zs D=execute zs D := by
  induction zs generalizing D with
  | nil => rfl
  | cons z zs ih => simp only [cachedExecute,execute,cachedUpdate_eq,ih]

/-- Thirteen alternating depth-two passes are a candidate for all
heights. The checker exits as soon as a plaquette domain is empty. -/
def capHeightCheck (h : Nat) : Bool :=
  cachedExecute (stripSchedule h 13 0) (initialBank h)

def capHeightsCheck : Bool :=
  (List.range 30).all (fun i => capHeightCheck (14+i))

theorem capHeightsCheck_sound (ok : capHeightsCheck=true) :
    ∀ h, 14≤h → h≤43 → ∃ zs : List (Update h), execute zs (initialBank h)=true := by
  intro h lo hi
  have inRange : h-14 ∈ List.range 30 := List.mem_range.mpr (by omega)
  have passed := List.all_eq_true.mp ok _ inRange
  change capHeightCheck (14+(h-14))=true at passed
  rw [show 14+(h-14)=h by omega] at passed
  exact ⟨stripSchedule h 13 0,(cachedExecute_eq _ _).symm.trans passed⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
