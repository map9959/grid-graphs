import GridGraphs.Geometry.GridDual

/-!
# Edge-labelled rectangular grids

`SimpleGraph.edgeSet` identifies an edge by its unordered endpoints.  Plane
tree-cotree arguments additionally need its orientation and its two incident
face occurrences, especially for parallel boundary edges in the dual.  This
module packages horizontal and vertical coordinate edges into one finite type.
-/

namespace GridGraphs

open SimpleGraph
open scoped Sym2

/-- A primal grid edge with its horizontal or vertical coordinate data. -/
inductive GridEdge (m n : Nat) where
  | horizontal (edge : HorizontalGridEdge m n)
  | vertical (edge : VerticalGridEdge m n)
  deriving DecidableEq, Fintype

namespace GridEdge

/-- Canonically ordered primal endpoints. -/
def primalEndpoints {m n : Nat} :
    GridEdge m n → GridVertex m n × GridVertex m n
  | .horizontal e => horizontalPrimalEndpoints e
  | .vertical e => verticalPrimalEndpoints e

/-- Canonically ordered incident faces.  Distinct grid edges remain distinct
even when they have the same pair of face names at the outer boundary. -/
def dualEndpoints {m n : Nat} :
    GridEdge m n → GridFace m n × GridFace m n
  | .horizontal e => horizontalDualEndpoints e
  | .vertical e => verticalDualEndpoints e

/-- The underlying unordered primal edge. -/
def primalSym2 {m n : Nat} (e : GridEdge m n) : Sym2 (GridVertex m n) :=
  s(e.primalEndpoints.1, e.primalEndpoints.2)

@[simp] theorem primalEndpoints_horizontal {m n : Nat}
    (e : HorizontalGridEdge m n) :
    primalEndpoints (.horizontal e) = horizontalPrimalEndpoints e := rfl

@[simp] theorem primalEndpoints_vertical {m n : Nat}
    (e : VerticalGridEdge m n) :
    primalEndpoints (.vertical e) = verticalPrimalEndpoints e := rfl

@[simp] theorem dualEndpoints_horizontal {m n : Nat}
    (e : HorizontalGridEdge m n) :
    dualEndpoints (.horizontal e) = horizontalDualEndpoints e := rfl

@[simp] theorem dualEndpoints_vertical {m n : Nat}
    (e : VerticalGridEdge m n) :
    dualEndpoints (.vertical e) = verticalDualEndpoints e := rfl

@[simp] theorem primalSym2_horizontal {m n : Nat}
    (e : HorizontalGridEdge m n) :
    primalSym2 (.horizontal e) =
      s((horizontalPrimalEndpoints e).1, (horizontalPrimalEndpoints e).2) := rfl

@[simp] theorem primalSym2_vertical {m n : Nat}
    (e : VerticalGridEdge m n) :
    primalSym2 (.vertical e) =
      s((verticalPrimalEndpoints e).1, (verticalPrimalEndpoints e).2) := rfl

end GridEdge

/-- Two horizontal coordinate edges with equal coordinates are equal. -/
theorem horizontalGridEdge_eq_of_row_eq_of_col_val_eq {m n : Nat}
    {e e' : HorizontalGridEdge m n} (hr : e.row = e'.row)
    (hc : e.col.val = e'.col.val) : e = e' := by
  cases e
  cases e'
  simp only [HorizontalGridEdge.mk.injEq]
  exact ⟨hr, Fin.ext hc⟩

/-- The unordered primal endpoints determine a horizontal coordinate edge. -/
theorem horizontalPrimalEndpoints_sym2_injective {m n : Nat} :
    Function.Injective (fun e : HorizontalGridEdge m n =>
      s((horizontalPrimalEndpoints e).1, (horizontalPrimalEndpoints e).2)) := by
  intro e e' h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · apply horizontalGridEdge_eq_of_row_eq_of_col_val_eq
    · simpa [horizontalPrimalEndpoints] using
        congrArg (fun x => x.1) h.1
    · simpa [horizontalPrimalEndpoints] using
        congrArg (fun x => x.2.val) h.1
  · have hcol : e.col.val = e'.col.val + 1 := by
      simpa [horizontalPrimalEndpoints] using
        congrArg (fun x => x.2.val) h.1
    have hcol' : e.col.val + 1 = e'.col.val := by
      simpa [horizontalPrimalEndpoints] using
        congrArg (fun x => x.2.val) h.2
    omega

/-- Horizontal and vertical coordinate edges never have the same unordered
primal endpoints. -/
theorem horizontalPrimalEndpoints_sym2_ne_vertical {m n : Nat}
    (e : HorizontalGridEdge m n) (e' : VerticalGridEdge m n) :
    s((horizontalPrimalEndpoints e).1, (horizontalPrimalEndpoints e).2) ≠
      s((verticalPrimalEndpoints e').1, (verticalPrimalEndpoints e').2) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · have hrow := congrArg (fun x : GridVertex m n => x.1.val) h.1
    have hrow' := congrArg (fun x : GridVertex m n => x.1.val) h.2
    simp [horizontalPrimalEndpoints, verticalPrimalEndpoints] at hrow hrow'
    omega
  · have hrow := congrArg (fun x : GridVertex m n => x.1.val) h.1
    have hrow' := congrArg (fun x : GridVertex m n => x.1.val) h.2
    simp [horizontalPrimalEndpoints, verticalPrimalEndpoints] at hrow hrow'
    omega

namespace GridEdge

/-- A coordinate grid edge is determined by its unordered primal endpoints. -/
theorem primalSym2_injective {m n : Nat} :
    Function.Injective (@primalSym2 m n) := by
  intro e e' h
  cases e with
  | horizontal a =>
      cases e' with
      | horizontal b =>
          congr 1
          exact horizontalPrimalEndpoints_sym2_injective h
      | vertical b =>
          exact (horizontalPrimalEndpoints_sym2_ne_vertical a b h).elim
  | vertical a =>
      cases e' with
      | horizontal b =>
          exact (horizontalPrimalEndpoints_sym2_ne_vertical b a h.symm).elim
      | vertical b =>
          congr 1
          exact verticalPrimalEndpoints_sym2_injective h

@[simp] theorem primalSym2_mem_gridGraph_edgeSet {m n : Nat}
    (e : GridEdge m n) :
    e.primalSym2 ∈ (gridGraph m n).edgeSet := by
  cases e with
  | horizontal e =>
      change s((horizontalPrimalEndpoints e).1,
        (horizontalPrimalEndpoints e).2) ∈ (gridGraph m n).edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact horizontalPrimalEndpoints_adj e
  | vertical e =>
      change s((verticalPrimalEndpoints e).1,
        (verticalPrimalEndpoints e).2) ∈ (gridGraph m n).edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact verticalPrimalEndpoints_adj e

/-- Edge-labelled coordinate edges are equivalent to the unordered edges of
the abstract grid graph, including degenerate rectangular grids. -/
noncomputable def equivGridGraphEdgeSet (m n : Nat) :
    GridEdge m n ≃ (gridGraph m n).edgeSet :=
  Equiv.ofBijective
    (fun e => ⟨e.primalSym2, primalSym2_mem_gridGraph_edgeSet e⟩)
    ⟨by
      intro e e' h
      apply primalSym2_injective
      exact congrArg Subtype.val h,
     by
      rintro ⟨edge, hedge⟩
      induction edge using Sym2.inductionOn with
      | _ v w =>
          rw [SimpleGraph.mem_edgeSet] at hedge
          rcases gridGraph_adj_exists_coordinate_edge hedge with h | h
          · obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
            · exact ⟨.horizontal e, rfl⟩
            · refine ⟨.horizontal e, Subtype.ext ?_⟩
              exact Sym2.eq_swap
          · obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
            · exact ⟨.vertical e, rfl⟩
            · refine ⟨.vertical e, Subtype.ext ?_⟩
              exact Sym2.eq_swap⟩

end GridEdge

end GridGraphs
