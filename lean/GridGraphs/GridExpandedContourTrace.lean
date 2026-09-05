import GridGraphs.GridExpandedContour

/-!
# Finite expanded-contour traces

An expanded-contour step either traverses one retained tree edge or turns in
place.  This module erases the in-place turns, retaining occupied steps as
directional darts and as an honest walk in the retained graph.
-/

namespace GridGraphs

open SimpleGraph
open scoped Sym2

namespace GridExpandedContour

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Endpoint slot after a finite expanded-contour interval.  This recursion is
oriented to expose the first step to the trace constructions below. -/
def advance (s : GridCompassSlot m n) : Nat → GridCompassSlot m n
  | 0 => s
  | k + 1 => advance (succ (T := T) s) k

/-- `advance` is the usual iterate of the expanded contour permutation. -/
theorem advance_eq_iterate (s : GridCompassSlot m n) (k : Nat) :
    advance (T := T) s k = ((equiv (T := T)^[k]) s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [advance, ih, Function.iterate_succ_apply]
      rfl

theorem advance_add (s : GridCompassSlot m n) (a b : Nat) :
    advance (T := T) (advance (T := T) s a) b =
      advance (T := T) s (a + b) := by
  rw [advance_eq_iterate, advance_eq_iterate, advance_eq_iterate,
    add_comm, Function.iterate_add_apply]

/-- Occupied steps of a finite expanded-contour interval, in traversal order.
Unoccupied in-place turns contribute no dart. -/
def occupiedDarts (s : GridCompassSlot m n) : Nat → List (GridDirectionalDart T)
  | 0 => []
  | k + 1 =>
      if hs : Occupied (T := T) s then
        GridDirectionalDart.ofDirectionMem (T := T) s.1 s.2 hs ::
          occupiedDarts (succ (T := T) s) k
      else
        occupiedDarts (succ (T := T) s) k

/-- Every collected item is, by construction, a retained directional dart of
`T`; this theorem exposes its adjacency field without unfolding the trace. -/
theorem adj_of_mem_occupiedDarts (s : GridCompassSlot m n) (k : Nat)
    {d : GridDirectionalDart T} (_hd : d ∈ occupiedDarts (T := T) s k) :
    T.Adj d.source d.target :=
  d.adj

/-- A retained directional dart as a dart of the abstract graph `T`. -/
def graphDart (d : GridDirectionalDart T) : T.Dart :=
  ⟨(d.source, d.target), d.adj⟩

/-- Erase expanded in-place turns and project occupied transitions to an
honest walk in `T`. -/
def walk (s : GridCompassSlot m n) :
    (k : Nat) → T.Walk s.1 (advance (T := T) s k).1
  | 0 => Walk.nil
  | k + 1 => by
      let t := succ (T := T) s
      let p := walk t k
      by_cases hs : Occupied (T := T) s
      · let d := GridDirectionalDart.ofDirectionMem (T := T) s.1 s.2 hs
        have ht : t.1 = d.target := by
          exact congrArg Prod.fst (succ_of_occupied hs)
        exact Walk.cons d.adj (p.copy ht rfl)
      · have ht : t.1 = s.1 := by
          simpa [t] using congrArg Prod.fst (succ_of_not_occupied hs)
        exact p.copy ht rfl

/-- Endpoint form using standard permutation iteration. -/
def iterateWalk (s : GridCompassSlot m n) (k : Nat) :
    T.Walk s.1 (((equiv (T := T)^[k]) s).1) :=
  (walk (T := T) s k).copy rfl (congrArg Prod.fst (advance_eq_iterate s k))

/-- The projected walk uses exactly the unordered edges of the occupied darts,
in the same order.  Thus consecutive non-stutter transitions join as a walk. -/
theorem edges_walk (s : GridCompassSlot m n) (k : Nat) :
    (walk (T := T) s k).edges =
      (occupiedDarts (T := T) s k).map GridDirectionalDart.edgeSym2 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      by_cases hs : Occupied (T := T) s
      · simp only [walk, occupiedDarts, dif_pos hs, List.map_cons,
          Walk.edges_cons, Walk.edges_copy]
        rw [ih]
        rfl
      · simp only [walk, occupiedDarts, dif_neg hs, Walk.edges_copy]
        exact ih (succ (T := T) s)

/-- Strong oriented form of `edges_walk`: after turns are erased, the
collected directional darts are exactly the consecutive darts of the walk. -/
theorem darts_walk (s : GridCompassSlot m n) (k : Nat) :
    (walk (T := T) s k).darts =
      (occupiedDarts (T := T) s k).map graphDart := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      by_cases hs : Occupied (T := T) s
      · simp only [walk, occupiedDarts, dif_pos hs, List.map_cons,
          Walk.darts_cons, Walk.darts_copy]
        rw [ih]
        rfl
      · simp only [walk, occupiedDarts, dif_neg hs, Walk.darts_copy]
        exact ih (succ (T := T) s)

/-- Standard-iterate projection has the same exact edge trace. -/
theorem edges_iterateWalk (s : GridCompassSlot m n) (k : Nat) :
    (iterateWalk (T := T) s k).edges =
      (occupiedDarts (T := T) s k).map GridDirectionalDart.edgeSym2 := by
  rw [iterateWalk, Walk.edges_copy, edges_walk]

/-- Standard-iterate projection has the same exact oriented dart trace. -/
theorem darts_iterateWalk (s : GridCompassSlot m n) (k : Nat) :
    (iterateWalk (T := T) s k).darts =
      (occupiedDarts (T := T) s k).map graphDart := by
  rw [iterateWalk, Walk.darts_copy, darts_walk]

end

end GridExpandedContour

end GridGraphs
