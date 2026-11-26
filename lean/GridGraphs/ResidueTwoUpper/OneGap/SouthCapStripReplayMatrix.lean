import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayCache

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan

abbrev MatrixBank := Array (Array (List Word))

@[noinline] def matrixOf (h : Nat) (D : Bank) : MatrixBank :=
  Array.ofFn fun r : Fin (h-1) =>
    Array.ofFn fun c : Fin (width h-1) => D r.val c.val

def matrixRead (m : MatrixBank) : Bank := fun r c =>
  ((m[r]?).bind (fun row => row[c]?)).getD []

theorem matrixRead_of (h : Nat) (D : Bank) (r c : Nat)
    (hr : r+2≤h) (hc : c+2≤width h) : matrixRead (matrixOf h D) r c=D r c := by
  simp only [matrixRead,matrixOf,Array.getElem?_ofFn,dif_pos (show r<h-1 by omega),
    Option.bind_some,dif_pos (show c<width h-1 by omega),Option.getD_some]

-- Keep the arrays as data across the recursive calls: saturating an
-- evaluator of type Nat → Nat → List Word can recompute its tables.
@[noinline] def applyMatrix {h : Nat} (z : Update h) (m : MatrixBank)
    (arcs : Array (List (Arc Line PackedPartition))) : MatrixBank :=
  matrixOf h fun r c => match localCell z.window r c with
    | none => matrixRead m r c
    | some (j,i) => arcWords z.window.axis arcs j i

def matrixUpdate {h : Nat} (z : Update h) (m : MatrixBank) : MatrixBank :=
  applyMatrix z m (cachedArcTable z (matrixRead m))

theorem matrixUpdate_read {h : Nat} (z : Update h) (m : MatrixBank) (r c : Nat)
    (hr : r+2≤h) (hc : c+2≤width h) :
    matrixRead (matrixUpdate z m) r c=updateBank z (matrixRead m) r c := by
  rw [←cachedUpdate_eq,matrixUpdate,applyMatrix,matrixRead_of _ _ _ _ hr hc]
  rfl

def matrixExecute {h : Nat} : List (Update h) → MatrixBank → Bool
  | [],m => (emptyCell h (matrixRead m)).isSome
  | z::zs,m => (emptyCell h (matrixRead m)).isSome || matrixExecute zs (matrixUpdate z m)

theorem matrix_cannot_reject {h : Nat} (lo : 14≤h) (zs : List (Update h)) (m : MatrixBank)
    (t : Tiles) (init : Admitted h (width h) (memBank (matrixRead m)) t)
    (traces : ∀ z∈zs, z.window.HasTrace (tileSweep (3*z.window.depth) z.window.axis
      (replayTooth z.window z.north) (replayExits z.window)) (band t z.window.axis z.window.start)) :
    matrixExecute zs m=false := by
  induction zs generalizing m with
  | nil => exact execute_cannot_reject lo [] (matrixRead m) t init traces
  | cons z zs ih =>
    have nonempty := execute_cannot_reject lo [] (matrixRead m) t init (by simp)
    change (emptyCell h (matrixRead m)).isSome=false at nonempty
    rw [matrixExecute,nonempty,Bool.false_or]
    apply ih
    · have keeps := survives_update z.window _ init (traces z (by simp))
      intro r c hr hc
      change word t r c ∈ matrixRead (matrixUpdate z m) r c
      rw [matrixUpdate_read _ _ _ _ hr hc]
      exact updateBank_sound z (length_ge2 lo _) r c _ (keeps r c hr hc)
    · exact fun z hz => traces z (List.mem_cons_of_mem _ hz)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
