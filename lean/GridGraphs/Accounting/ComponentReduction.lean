import GridGraphs.Accounting.ForcedForestLedger
import GridGraphs.Core.Spanning

/-!
# Component reduction for forced grid vertices

The restricted handshaking identity counts an edge once when exactly one of
its endpoints lies in `F`, and twice when both endpoints lie in `F`.  The two
forest ledgers then turn those two edge counts into component counts.
-/

namespace GridGraphs

open Finset SimpleGraph
open scoped Sym2

set_option maxHeartbeats 800000

variable {V : Type*}

/-- Restricted handshaking: degrees on `F` count every forced edge once and
every edge internal to `F` once more. -/
theorem sum_degrees_finset_eq_forced_add_induced
    (G : SimpleGraph V) (F : Finset V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (∑ v ∈ F, G.degree v) =
      (forcedEdgeGraph G (↑F : Set V)).edgeFinset.card +
        (G.induce (↑F : Set V)).edgeFinset.card := by
  classical
  let containsF : Sym2 V → Nat := fun e => ∑ v ∈ F, if v ∈ e then 1 else 0
  have hdegree (v : V) :
      G.degree v = ∑ e ∈ G.edgeFinset, if v ∈ e then 1 else 0 := by
    rw [← G.card_incidenceFinset_eq_degree]
    rw [G.incidenceFinset_eq_filter]
    exact (Finset.sum_boole (fun e => v ∈ e) G.edgeFinset).symm
  have hsum : (∑ v ∈ F, G.degree v) = ∑ e ∈ G.edgeFinset, containsF e := by
    simp_rw [hdegree]
    rw [Finset.sum_comm]
  have hforced :
      (forcedEdgeGraph G (↑F : Set V)).edgeFinset =
        G.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ F) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ v w =>
        simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
        simp [forcedEdgeGraph, Sym2.mem_iff]
  have hinduced :
      (G.induce (↑F : Set V)).edgeFinset.card =
        (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ F)).card := by
    have hmap := G.map_edgeFinset_induce (s := (↑F : Set V))
    have hcard := congrArg Finset.card hmap
    rw [Finset.card_map] at hcard
    calc
      (G.induce (↑F : Set V)).edgeFinset.card =
          (G.edgeFinset ∩ (↑F : Set V).toFinset.sym2).card := by
            convert hcard using 1 <;> congr 1 <;> ext e <;> simp
      _ = (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ F)).card := by
        congr 1
        ext e
        induction e using Sym2.inductionOn with
        | _ v w => simp [Sym2.mem_iff]
  rw [hsum, hforced, hinduced]
  have hor :
      (G.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ F)).card =
        ∑ e ∈ G.edgeFinset, if ∃ v ∈ e, v ∈ F then 1 else 0 :=
    (Finset.sum_boole (R := Nat) (fun e => ∃ v ∈ e, v ∈ F) G.edgeFinset).symm
  have hand :
      (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ F)).card =
        ∑ e ∈ G.edgeFinset, if ∀ v ∈ e, v ∈ F then 1 else 0 :=
    (Finset.sum_boole (R := Nat) (fun e => ∀ v ∈ e, v ∈ F) G.edgeFinset).symm
  rw [hor, hand, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ v w =>
      rw [SimpleGraph.mem_edgeFinset] at he
      have hvw : v ≠ w := G.ne_of_adj he
      simp only [containsF, Sym2.mem_iff]
      rw [Finset.sum_boole]
      by_cases hv : v ∈ F
      · by_cases hw : w ∈ F
        · rw [show F.filter (fun x => x = v ∨ x = w) = {v, w} by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · exact fun h => h.2
            · intro h
              rcases h with rfl | rfl <;> simp [hv, hw]]
          simp [hvw, hv, hw]
        · rw [show F.filter (fun x => x = v ∨ x = w) = {v} by
            ext x
            simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨hx, rfl | rfl⟩
              · rfl
              · exact absurd hx hw
            · intro h
              rw [h]
              exact ⟨hv, Or.inl rfl⟩]
          simp [hv, hw]
      · by_cases hw : w ∈ F
        · rw [show F.filter (fun x => x = v ∨ x = w) = {w} by
            ext x
            simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨hx, rfl | rfl⟩
              · exact absurd hx hv
              · rfl
            · intro h
              rw [h]
              exact ⟨hw, Or.inr rfl⟩]
          simp [hv, hw]
        · rw [show F.filter (fun x => x = v ∨ x = w) = ∅ by
            ext x
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
            rintro ⟨hx, rfl | rfl⟩
            · exact hv hx
            · exact hw hx]
          simp [hv, hw]

/-- Deficiency from the ambient degree-four grid bound. -/
def gridBoundaryDeficiency (m n : Nat) (v : GridVertex m n) : Nat :=
  4 - (gridGraph m n).degree v

/-- Total boundary deficiency on a finite set of grid vertices. -/
def boundaryDeficiencySum (m n : Nat) (F : Finset (GridVertex m n)) : Nat :=
  ∑ v ∈ F, gridBoundaryDeficiency m n v

/-- The degree and boundary-deficiency contributions on `F` add to `4|F|`. -/
lemma sum_degrees_add_boundaryDeficiencySum (m n : Nat)
    (F : Finset (GridVertex m n)) :
    (∑ v ∈ F, (gridGraph m n).degree v) + boundaryDeficiencySum m n F =
      4 * F.card := by
  unfold boundaryDeficiencySum gridBoundaryDeficiency
  rw [← Finset.sum_add_distrib]
  calc
    ∑ v ∈ F, ((gridGraph m n).degree v +
        (4 - (gridGraph m n).degree v)) = ∑ _v ∈ F, 4 := by
      apply Finset.sum_congr rfl
      intro v _
      exact Nat.add_sub_of_le (gridGraph_degree_le_four m n v)
    _ = 4 * F.card := by simp [mul_comm]

/-- The total boundary deficiency of a nondegenerate rectangular grid is its
perimeter. -/
theorem total_boundaryDeficiencySum {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    boundaryDeficiencySum m n Finset.univ = 2 * m + 2 * n := by
  have hdef := sum_degrees_add_boundaryDeficiencySum m n
    (Finset.univ : Finset (GridVertex m n))
  rw [sum_gridGraph_degree] at hdef
  simp only [Finset.card_univ, GridVertex, Fintype.card_prod,
    Fintype.card_fin] at hdef
  unfold numEdges numHoriz numVert at hdef
  simp only [Nat.mul_sub_left_distrib, mul_one] at hdef
  rw [Nat.mul_comm n m] at hdef
  have hmprod : m ≤ m * n := by
    simpa using Nat.mul_le_mul_left m (show 1 ≤ n by omega)
  have hnprod : n ≤ m * n := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left n (show 1 ≤ m by omega)
  omega

/-- Boundary deficiency partitions over a finset and its complement. -/
lemma boundaryDeficiencySum_add_compl (m n : Nat)
    (U : Finset (GridVertex m n)) :
    boundaryDeficiencySum m n U +
        boundaryDeficiencySum m n (Finset.univ \ U) =
      boundaryDeficiencySum m n Finset.univ := by
  unfold boundaryDeficiencySum
  rw [← Finset.sum_union Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset (Finset.subset_univ U)]

/-- A grid finset and its complement partition all `m * n` vertices. -/
lemma card_compl_add_card_grid (m n : Nat) (U : Finset (GridVertex m n)) :
    (Finset.univ \ U).card + U.card = m * n := by
  simpa [GridVertex] using
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)

/-- Exact component identity for an acyclic forced-edge graph. -/
theorem grid_component_reduction {m n : Nat} (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    3 * F.card +
        Fintype.card
          ((gridGraph m n).induce
            (↑F : Set (GridVertex m n))).ConnectedComponent +
        Fintype.card (forcedEdgeGraph (gridGraph m n)
          (↑F : Set (GridVertex m n))).ConnectedComponent =
      m * n + boundaryDeficiencySum m n F := by
  have hrestricted :=
    sum_degrees_finset_eq_forced_add_induced (gridGraph m n) F
  have hinduced := induce_finset_forest_ledger (gridGraph m n) F hH
  have hforced := grid_forcedEdgeGraph_forest_ledger m n F hH
  have hdef := sum_degrees_add_boundaryDeficiencySum m n F
  omega

/-- Subtraction-free row-prefix form of `grid_component_reduction`.  The row
charge `n + 3 - 3|F_row|`, summed over `m` rows, is represented by moving its
forced-vertex term to the left. -/
theorem grid_prefix_component_ledger {m n : Nat}
    (F : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic) :
    3 * F.card + 3 * m +
          Fintype.card
            ((gridGraph m n).induce
              (↑F : Set (GridVertex m n))).ConnectedComponent +
          Fintype.card (forcedEdgeGraph (gridGraph m n)
            (↑F : Set (GridVertex m n))).ConnectedComponent =
      m * (n + 3) + boundaryDeficiencySum m n F := by
  have h := grid_component_reduction F hH
  rw [Nat.mul_add, Nat.mul_comm m 3]
  omega

/-- Exact subtraction-free component identity when the forced vertices are the
complement of `U`. -/
theorem grid_component_reduction_compl {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (U : Finset (GridVertex m n))
    (hH : (forcedEdgeGraph (gridGraph m n)
      (↑(Finset.univ \ U) : Set (GridVertex m n))).IsAcyclic) :
    boundaryDeficiencySum m n U +
        Fintype.card
          ((gridGraph m n).induce
            (↑(Finset.univ \ U) : Set (GridVertex m n))).ConnectedComponent +
        Fintype.card
          (forcedEdgeGraph (gridGraph m n)
            (↑(Finset.univ \ U) : Set (GridVertex m n))).ConnectedComponent +
        2 * (m * n) =
      3 * U.card + 2 * m + 2 * n := by
  have hreduction := grid_component_reduction (Finset.univ \ U) hH
  have hboundary := boundaryDeficiencySum_add_compl m n U
  have htotal := total_boundaryDeficiencySum hm hn
  have hcard := card_compl_add_card_grid m n U
  omega

/-- Square specialization of `grid_component_reduction_compl`. -/
theorem square_grid_component_reduction_compl {n : Nat} (hn : 2 ≤ n)
    (U : Finset (GridVertex n n))
    (hH : (forcedEdgeGraph (gridGraph n n)
      (↑(Finset.univ \ U) : Set (GridVertex n n))).IsAcyclic) :
    boundaryDeficiencySum n n U +
        Fintype.card
          ((gridGraph n n).induce
            (↑(Finset.univ \ U) : Set (GridVertex n n))).ConnectedComponent +
        Fintype.card
          (forcedEdgeGraph (gridGraph n n)
            (↑(Finset.univ \ U) : Set (GridVertex n n))).ConnectedComponent +
        2 * (n * n) =
      3 * U.card + 4 * n := by
  have h := grid_component_reduction_compl hn hn U hH
  omega

end GridGraphs
