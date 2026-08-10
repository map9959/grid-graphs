import GridGraphs.CanonicalShoreGerms
import GridGraphs.GridShoreChannelForest

/-!
# Continuing canonical shore germs

Canonical germs not supported by the cotree enter along a retained inward tree
edge.  This file constructs those edges and their unique rooted orientations.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

namespace OuterBoundarySide

def inwardDirection : OuterBoundarySide → GridDirection
  | .top => .south
  | .bottom => .north
  | .left => .east
  | .right => .west

end OuterBoundarySide

namespace CanonicalShoreDemand

/-- The first interior vertex reached by a canonical boundary germ. -/
def inwardTarget {n : Nat} (axis : ShoreSweepAxis) (hn : 2 ≤ n) :
    CanonicalShoreDemand axis n → GridVertex n n :=
  match axis with
  | .rows => fun q => match q with
      | .inl r => (r, ⟨1, by omega⟩)
      | .inr i =>
          if i.val = 0 then
            (⟨1, by omega⟩, ⟨n - 1, by omega⟩)
          else if i.val = 1 then
            (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)
          else
            (⟨n - 2, by omega⟩, ⟨0, by omega⟩)
  | .columns => fun q => match q with
      | .inl c => (⟨1, by omega⟩, c)
      | .inr i =>
          if i.val = 0 then
            (⟨0, by omega⟩, ⟨n - 2, by omega⟩)
          else if i.val = 1 then
            (⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩)
          else
            (⟨n - 1, by omega⟩, ⟨1, by omega⟩)

@[simp] theorem boundaryIncidence_inward_step {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (q : CanonicalShoreDemand axis n) :
    gridNeighbor? (boundaryIncidence axis hn q).1
        (boundaryIncidence axis hn q).2.inwardDirection =
      some (inwardTarget axis hn q) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  cases axis with
  | rows =>
      rcases q with q | q
      · simp [boundaryIncidence, inwardTarget, OuterBoundarySide.inwardDirection,
          gridNeighbor?] <;> omega
      · fin_cases q <;>
          simp [boundaryIncidence, inwardTarget, OuterBoundarySide.inwardDirection,
            gridNeighbor?] <;> omega
  | columns =>
      rcases q with q | q
      · simp [boundaryIncidence, inwardTarget, OuterBoundarySide.inwardDirection,
          gridNeighbor?] <;> omega
      · fin_cases q <;>
          simp [boundaryIncidence, inwardTarget, OuterBoundarySide.inwardDirection,
            gridNeighbor?] <;> omega

/-- The unordered physical edge used by the germ's first inward step. -/
def inwardEdgeSym2 {n : Nat} (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (q : CanonicalShoreDemand axis n) : Sym2 (GridVertex n n) :=
  s((boundaryIncidence axis hn q).1, inwardTarget axis hn q)

/-- Distinct side-labelled canonical germs have distinct inward edges. -/
theorem inwardEdgeSym2_injective {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n) (hn3 : 3 ≤ n) :
    Function.Injective (inwardEdgeSym2 axis hn) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn3
  intro a b hab
  simp only [inwardEdgeSym2] at hab
  cases axis with
  | rows =>
      rcases a with a | a <;> rcases b with b | b
      · congr 1
        rw [Sym2.eq_iff] at hab
        rcases hab with ⟨hl, _⟩ | ⟨hl, _⟩
        · exact congrArg Prod.fst hl
        · have hl' := congrArg (fun v : GridVertex (3 + d) (3 + d) => v.2.val) hl
          simp [inwardEdgeSym2, boundaryIncidence, inwardTarget] at hl'
      · fin_cases b <;> rw [Sym2.eq_iff] at hab <;>
          simp [inwardEdgeSym2, boundaryIncidence, inwardTarget] at hab
        all_goals
          rcases hab with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> exfalso
          all_goals
            have hl' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hl
            have hr' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hr
            simp at hl' hr' <;> omega
      · fin_cases a <;> rw [Sym2.eq_iff] at hab <;>
          simp [inwardEdgeSym2, boundaryIncidence, inwardTarget] at hab
        all_goals
          rcases hab with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> exfalso
          all_goals
            have hl' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hl
            have hr' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hr
            simp at hl' hr' <;> omega
      · fin_cases a <;> fin_cases b <;> try rfl
        all_goals
          rw [Sym2.eq_iff] at hab
          simp [inwardEdgeSym2, boundaryIncidence, inwardTarget] at hab
          rcases hab with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> exfalso
          all_goals
            have hl' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hl
            have hr' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hr
            simp at hl' hr' <;> omega
  | columns =>
      rcases a with a | a <;> rcases b with b | b
      · congr 1
        rw [Sym2.eq_iff] at hab
        rcases hab with ⟨hl, _⟩ | ⟨hl, _⟩
        · exact congrArg Prod.snd hl
        · have hl' := congrArg (fun v : GridVertex (3 + d) (3 + d) => v.1.val) hl
          simp [inwardEdgeSym2, boundaryIncidence, inwardTarget] at hl'
      · fin_cases b <;> rw [Sym2.eq_iff] at hab <;>
          simp [inwardEdgeSym2, boundaryIncidence, inwardTarget] at hab
        all_goals
          rcases hab with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> exfalso
          all_goals
            have hl' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hl
            have hr' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hr
            simp at hl' hr' <;> omega
      · fin_cases a <;> rw [Sym2.eq_iff] at hab <;>
          simp [inwardEdgeSym2, boundaryIncidence, inwardTarget] at hab
        all_goals
          rcases hab with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> exfalso
          all_goals
            have hl' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hl
            have hr' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hr
            simp at hl' hr' <;> omega
      · fin_cases a <;> fin_cases b <;> try rfl
        all_goals
          rw [Sym2.eq_iff] at hab
          simp [inwardEdgeSym2, boundaryIncidence, inwardTarget] at hab
          rcases hab with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> exfalso
          all_goals
            have hl' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hl
            have hr' := congrArg
              (fun v : GridVertex (3 + d) (3 + d) => (v.1.val, v.2.val)) hr
            simp at hl' hr' <;> omega

/-- Canonical demands that do not terminate directly at cotree support. -/
abbrev Unsupported {n : Nat} (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj] :=
  ↥((Finset.univ : Finset (CanonicalShoreDemand axis n)) \ directExits axis hn T)

theorem unsupported_boundary_not_mem_support {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj]
    (q : Unsupported axis hn T) :
    (boundaryIncidence axis hn q.1).1 ∉
      supportFinset (gridGraph n n \ T) := by
  intro hsupport
  exact (Finset.mem_sdiff.mp q.2).2
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupport⟩)

theorem unsupported_boundary_preserves {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (q : Unsupported axis hn T) :
    preservesIncidentEdges (gridGraph n n) T
      (boundaryIncidence axis hn q.1).1 := by
  by_contra hnot
  exact unsupported_boundary_not_mem_support axis hn T q
    ((mem_supportFinset_sdiff_iff_not_preserves
      (gridGraph n n) T hT.le _).mpr hnot)

end CanonicalShoreDemand

namespace GridDirectionalDart

/-- The retained inward dart of a canonical germ that did not exit directly. -/
noncomputable def retainedCanonicalInwardDart {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (q : CanonicalShoreDemand.Unsupported axis hn T) :
    GridDirectionalDart T where
  source := (CanonicalShoreDemand.boundaryIncidence axis hn q.1).1
  direction :=
    (CanonicalShoreDemand.boundaryIncidence axis hn q.1).2.inwardDirection
  target := CanonicalShoreDemand.inwardTarget axis hn q.1
  step := CanonicalShoreDemand.boundaryIncidence_inward_step axis hn q.1
  adj := CanonicalShoreDemand.unsupported_boundary_preserves axis hn hT q
    (gridNeighbor?_adj
      (CanonicalShoreDemand.boundaryIncidence_inward_step axis hn q.1))

@[simp] theorem retainedCanonicalInwardDart_edgeSym2 {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (q : CanonicalShoreDemand.Unsupported axis hn T) :
    (retainedCanonicalInwardDart axis hn hT q).edgeSym2 =
      CanonicalShoreDemand.inwardEdgeSym2 axis hn q.1 := rfl

/-- Choose the unique orientation of a tree edge pointing away from `root`. -/
noncomputable def rootedOrientation {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (htree : T.IsTree) (root : GridVertex m n) (d : GridDirectionalDart T) :
    RootedTreeDart (T := T) root := by
  classical
  exact if h : AwayFromRoot root d then ⟨d, h⟩ else
    ⟨d.reverse, (awayFromRoot_reverse_iff_not htree root d).2 h⟩

@[simp] theorem rootedOrientation_edgeSym2 {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (htree : T.IsTree) (root : GridVertex m n) (d : GridDirectionalDart T) :
    (rootedOrientation htree root d).1.edgeSym2 = d.edgeSym2 := by
  classical
  unfold rootedOrientation
  split
  · rfl
  · simp [edgeSym2, reverse, Sym2.eq_swap]

/-- Unsupported canonical germs launch at distinct rooted shore positions. -/
noncomputable def launchedShoreEmbedding {n : Nat}
    (axis : ShoreSweepAxis) (hn : 2 ≤ n) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (root : GridVertex n n) :
    CanonicalShoreDemand.Unsupported axis hn T ↪ RootedTreeDart (T := T) root where
  toFun q := rootedOrientation hT.isTree root
    (retainedCanonicalInwardDart axis hn hT q)
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply CanonicalShoreDemand.inwardEdgeSym2_injective axis hn hn3
    rw [← retainedCanonicalInwardDart_edgeSym2 axis hn hT a,
      ← retainedCanonicalInwardDart_edgeSym2 axis hn hT b]
    rw [← rootedOrientation_edgeSym2 hT.isTree root
      (retainedCanonicalInwardDart axis hn hT a),
      ← rootedOrientation_edgeSym2 hT.isTree root
        (retainedCanonicalInwardDart axis hn hT b)]
    exact congrArg (fun d : RootedTreeDart (T := T) root => d.1.edgeSym2) hab

end GridDirectionalDart

end GridGraphs
