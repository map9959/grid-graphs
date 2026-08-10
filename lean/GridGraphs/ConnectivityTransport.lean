import Mathlib

/-!
# Connectivity transport along path-valued graph maps

An adjacency need not map to one adjacency: subdivision or geometric insertion
may replace it by a path.  Connectivity still transports when every target
vertex can reach the image of a source vertex.
-/

namespace GridGraphs

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A map sending every source adjacency to a target path sends every source
path to a target path. -/
theorem reachable_map_of_adj_reachable (f : V → W)
    (hadj : ∀ {x y}, G.Adj x y → H.Reachable (f x) (f y))
    {x y : V} (hxy : G.Reachable x y) : H.Reachable (f x) (f y) := by
  refine hxy.elim ?_
  intro p
  induction p with
  | nil => exact Reachable.refl _
  | cons h p ih => exact (hadj h).trans (ih p.reachable)

/-- Connectivity transports through a path-valued map when every target
vertex attaches to some point in the source image. -/
theorem connected_of_reachable_map_of_attaches
    (f : V → W) (hG : G.Connected)
    (hadj : ∀ {x y}, G.Adj x y → H.Reachable (f x) (f y))
    (attaches : ∀ z : W, ∃ x : V, H.Reachable z (f x)) : H.Connected := by
  rw [SimpleGraph.connected_iff] at hG ⊢
  constructor
  · intro x z
    obtain ⟨y, hxy⟩ := attaches x
    obtain ⟨w, hzw⟩ := attaches z
    exact hxy.trans
      ((reachable_map_of_adj_reachable f hadj (hG.1 y w)).trans hzw.symm)
  · exact hG.2.map f

end GridGraphs
