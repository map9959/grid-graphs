import GridGraphs.Accounting.ResidueTwoNearWasteDebt
import GridGraphs.Accounting.ResidueTwoWasteEqualityBasic

/-!
# Width-independent component ports for stable residue-two debt

This module isolates a geometric fact needed by an OUT-rooted phase argument.
Every component of an induced silent set has a port in its complement whenever
the ambient graph is connected and the complement is nonempty.  The proof
follows an ambient path from the component to the outside and takes its first
crossing; it has no width census or finite search.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {V : Type*}

/-- Complement vertices adjacent to a fixed component of the graph induced by
`F`.  These are the component's available attachment ports. -/
noncomputable def inducedComponentPorts (G : SimpleGraph V) (F : Finset V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : (G.induce (↑F : Set V)).ConnectedComponent) : Finset V :=
  Finset.univ.filter fun u =>
    u ∉ F ∧ ∃ x : (↑F : Set V), x ∈ C.supp ∧ G.Adj x.1 u

/-- A component of a proper induced silent set has strictly positive port
debt.  This statement is independent of the size or shape of the ambient
graph. -/
theorem one_le_inducedComponentPorts_card (G : SimpleGraph V) (F : Finset V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.Connected) (hout : ∃ u : V, u ∉ F)
    (C : (G.induce (↑F : Set V)).ConnectedComponent) :
    1 ≤ (inducedComponentPorts G F C).card := by
  classical
  obtain ⟨x, hxC⟩ := C.nonempty_supp
  obtain ⟨u, huF⟩ := hout
  obtain ⟨p⟩ := hG x.1 u
  let rec firstPort {a b : V} (p : G.Walk a b)
      (haF : a ∈ F)
      (haC : (⟨a, haF⟩ : (↑F : Set V)) ∈ C.supp)
      (hbF : b ∉ F) :
      ∃ z : V, z ∉ F ∧
        ∃ y : (↑F : Set V), y ∈ C.supp ∧ G.Adj y.1 z := by
    cases p with
    | nil => exact (hbF haF).elim
    | @cons _ c _ hac p =>
        by_cases hcF : c ∈ F
        · have hac' : (G.induce (↑F : Set V)).Adj
              (⟨a, haF⟩ : (↑F : Set V)) ⟨c, hcF⟩ := hac
          exact firstPort p hcF (C.mem_supp_of_adj_mem_supp haC hac') hbF
        · exact ⟨c, hcF, ⟨a, haF⟩, haC, hac⟩
  obtain ⟨z, hzF, y, hyC, hyz⟩ := firstPort p x.property hxC huF
  rw [Finset.one_le_card]
  refine ⟨z, ?_⟩
  simp only [inducedComponentPorts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hzF, y, hyC, hyz⟩

/-- Directed edges crossing from the complement of `F` into `F`.  Orienting
the edges makes the outside endpoint available for degree counting. -/
noncomputable def inducedComponentCrossingEdges (G : SimpleGraph V)
    (F : Finset V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    Finset (Σ _u : V, V) :=
  (Finset.univ \ F).sigma fun u => (G.neighborFinset u).filter fun x => x ∈ F

/-- First crossings belonging to different induced components are different
edges.  Consequently the complete crossing-edge set has at least as many
edges as `G[F]` has components. -/
theorem card_connectedComponent_le_inducedComponentCrossingEdges_card
    (G : SimpleGraph V) (F : Finset V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.Connected) (hout : ∃ u : V, u ∉ F) :
    Fintype.card (G.induce (↑F : Set V)).ConnectedComponent ≤
      (inducedComponentCrossingEdges G F).card := by
  classical
  let K := (G.induce (↑F : Set V)).ConnectedComponent
  have hchoice (C : K) : ∃ e : Σ _u : V, V,
      e ∈ inducedComponentCrossingEdges G F ∧
        ∃ hxF : e.2 ∈ F, (⟨e.2, hxF⟩ : (↑F : Set V)) ∈ C.supp := by
    have hport := one_le_inducedComponentPorts_card G F hG hout C
    rw [Finset.one_le_card] at hport
    obtain ⟨u, hu⟩ := hport
    have hudata : u ∉ F ∧
        ∃ x : (↑F : Set V), x ∈ C.supp ∧ G.Adj x.1 u := by
      simpa only [inducedComponentPorts, Finset.mem_filter, Finset.mem_univ,
        true_and] using hu
    obtain ⟨huF, x, hxC, hxu⟩ := hudata
    refine ⟨⟨u, x.1⟩, ?_, x.property, hxC⟩
    simp [inducedComponentCrossingEdges, huF, hxu.symm]
  let edge (C : K) : Σ _u : V, V := Classical.choose (hchoice C)
  have hedge (C : K) : edge C ∈ inducedComponentCrossingEdges G F :=
    (Classical.choose_spec (hchoice C)).1
  let crossing (C : K) : ↥(inducedComponentCrossingEdges G F) :=
    ⟨edge C, hedge C⟩
  have hinjective : Function.Injective crossing := by
    intro C D hCD
    have hedgeEq : edge C = edge D := congrArg Subtype.val hCD
    have hxEq : (edge C).2 = (edge D).2 :=
      congrArg (fun e : Σ _u : V, V => e.2) hedgeEq
    obtain ⟨hxCF, hxC⟩ := (Classical.choose_spec (hchoice C)).2
    obtain ⟨hxDF, hxD⟩ := (Classical.choose_spec (hchoice D)).2
    have hxD' : (⟨(edge C).2, hxCF⟩ : (↑F : Set V)) ∈ D.supp := by
      simpa only [hxEq] using hxD
    exact ConnectedComponent.eq_of_common_vertex hxC hxD'
  simpa only [K, Fintype.card_coe] using Fintype.card_le_of_injective crossing hinjective

/-- Every crossing edge uses one neighbor slot at its outside endpoint. -/
theorem inducedComponentCrossingEdges_card_le_sum_degree
    (G : SimpleGraph V) (F : Finset V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (inducedComponentCrossingEdges G F).card ≤
      ∑ u ∈ Finset.univ \ F, G.degree u := by
  classical
  rw [inducedComponentCrossingEdges, Finset.card_sigma]
  apply Finset.sum_le_sum
  intro u hu
  exact Finset.card_filter_le _ _

/-- Grid degree four turns disjoint first crossings into a global component
inequality involving distinct directed edges, rather than merely a separate
nonemptiness assertion for every component. -/
theorem grid_inducedComponent_count_le_four_mul_complement_card
    {m n : Nat} (F : Finset (GridVertex m n))
    (hconn : (gridGraph m n).Connected) (hout : ∃ u, u ∉ F) :
    Fintype.card ((gridGraph m n).induce
        (↑F : Set (GridVertex m n))).ConnectedComponent ≤
      4 * ((Finset.univ : Finset (GridVertex m n)) \ F).card := by
  classical
  have hcross := card_connectedComponent_le_inducedComponentCrossingEdges_card
    (gridGraph m n) F hconn hout
  have hdegree := inducedComponentCrossingEdges_card_le_sum_degree
    (gridGraph m n) F
  have hsum : (∑ u ∈ (Finset.univ : Finset (GridVertex m n)) \ F,
      (gridGraph m n).degree u) ≤
      4 * ((Finset.univ : Finset (GridVertex m n)) \ F).card := by
    calc
      (∑ u ∈ (Finset.univ : Finset (GridVertex m n)) \ F,
          (gridGraph m n).degree u) ≤
          ∑ _u ∈ (Finset.univ : Finset (GridVertex m n)) \ F, 4 := by
            apply Finset.sum_le_sum
            intro u hu
            exact gridGraph_degree_le_four m n u
      _ = 4 * ((Finset.univ : Finset (GridVertex m n)) \ F).card := by
        simp [Nat.mul_comm]
  omega

/-- In the hypothetical stable residue-two support profile, every component of
the full-vertex graph has at least one support port.  This is the strict
width-independent component debt available before any phase classification. -/
theorem residueTwo_stable_fullComponent_has_supportPort
    (k : Nat) (hk : 5 ≤ k)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (_hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (hcard : (residueTwoCotreeSupport T).card = 6 * k ^ 2 + 5 * k + 3)
    (C : ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑(residueTwoFullSet T) :
        Set (GridVertex (3 * k + 2) (3 * k + 2)))).ConnectedComponent) :
    1 ≤ ((inducedComponentPorts
      (gridGraph (3 * k + 2) (3 * k + 2)) (residueTwoFullSet T) C) ∩
        residueTwoCotreeSupport T).card := by
  classical
  have hU : (residueTwoCotreeSupport T).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hz : (residueTwoCotreeSupport T).card = 0 := by rw [hempty]; simp
    omega
  have hports := one_le_inducedComponentPorts_card
    (gridGraph (3 * k + 2) (3 * k + 2)) (residueTwoFullSet T)
    (gridGraph_connected (by omega) (by omega)) (by
      obtain ⟨u, huU⟩ := hU
      refine ⟨u, ?_⟩
      simp only [residueTwoFullSet, Finset.mem_sdiff, Finset.mem_univ, true_and,
        not_not]
      exact huU) C
  rw [show inducedComponentPorts
      (gridGraph (3 * k + 2) (3 * k + 2)) (residueTwoFullSet T) C ∩
        residueTwoCotreeSupport T =
      inducedComponentPorts
        (gridGraph (3 * k + 2) (3 * k + 2)) (residueTwoFullSet T) C by
    apply Finset.inter_eq_left.mpr
    intro u hu
    have hudata : u ∉ residueTwoFullSet T ∧
        ∃ x : (↑(residueTwoFullSet T) :
          Set (GridVertex (3 * k + 2) (3 * k + 2))),
          x ∈ C.supp ∧
            (gridGraph (3 * k + 2) (3 * k + 2)).Adj x.1 u := by
      simpa only [inducedComponentPorts, Finset.mem_filter, Finset.mem_univ,
        true_and] using hu
    have huout : u ∉ residueTwoFullSet T := hudata.1
    simpa only [residueTwoFullSet, Finset.mem_sdiff, Finset.mem_univ, true_and,
      not_not] using huout]
  exact hports

end GridGraphs
