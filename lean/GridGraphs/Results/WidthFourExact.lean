import GridGraphs.Core.ForcedMaximum
import GridGraphs.Constructions.WidthFourLower
import GridGraphs.Accounting.CheckerboardComponent
import GridGraphs.Accounting.PerimeterWaste
import GridGraphs.Accounting.LinearWaste

/-!
# Exact full-degree maximum on `4 x n` grids

The omitted-edge graph is bipartite. On each checkerboard color its incidence
waste is a multiple of three. One omitted perimeter edge makes both color
wastes positive, forcing at least `n` non-full vertices of each color.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- Incidence waste restricted to a specified vertex set. -/
def incidenceWasteOn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Nat :=
  ∑ v ∈ supportFinset G ∩ C, (3 - G.degree v)

theorem incidenceWasteOn_add_degreeSum {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hdegree : ∀ v, G.degree v ≤ 3) :
    incidenceWasteOn G C + ∑ v ∈ supportFinset G ∩ C, G.degree v =
      3 * (supportFinset G ∩ C).card := by
  unfold incidenceWasteOn
  rw [← Finset.sum_add_distrib]
  calc
    ∑ v ∈ supportFinset G ∩ C, (3 - G.degree v + G.degree v) =
        ∑ _v ∈ supportFinset G ∩ C, 3 := by
          apply Finset.sum_congr rfl
          intro v _
          have := hdegree v
          omega
    _ = 3 * (supportFinset G ∩ C).card := by simp [Nat.mul_comm]

theorem sum_degrees_support_inter_eq {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) :
    ∑ v ∈ supportFinset G ∩ C, G.degree v = ∑ v ∈ C, G.degree v := by
  apply Finset.sum_subset (Finset.inter_subset_right)
  intro v hvC hvnot
  have hvnotSupport : v ∉ supportFinset G := by
    intro hvSupport
    exact hvnot (Finset.mem_inter.mpr ⟨hvSupport, hvC⟩)
  rw [mem_supportFinset] at hvnotSupport
  omega

/-- Every subgraph of the checkerboard grid retains its checkerboard
bipartition. -/
theorem isBipartiteWith_checkerboard_of_le_gridGraph
    {m n : Nat} (G : SimpleGraph (GridVertex m n))
    (hG : G ≤ gridGraph m n) :
    G.IsBipartiteWith
      (↑(gridBlack m n) : Set (GridVertex m n))
      (↑(gridWhite m n) : Set (GridVertex m n)) := by
  have hgrid := gridGraph_isBipartiteWith_checkerboard m n
  constructor
  · exact hgrid.disjoint
  · intro v w hvw
    exact hgrid.mem_of_adj (hG hvw)

/-- A cotree has one degree incidence on each checkerboard color per edge. -/
theorem sum_degrees_gridBlack_eq_card_edges_of_le_gridGraph
    {m n : Nat} (G : SimpleGraph (GridVertex m n))
    [DecidableRel G.Adj] (hG : G ≤ gridGraph m n) :
    (∑ v ∈ gridBlack m n, G.degree v) = G.edgeFinset.card := by
  exact SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    (isBipartiteWith_checkerboard_of_le_gridGraph G hG)

theorem sum_degrees_gridWhite_eq_card_edges_of_le_gridGraph
    {m n : Nat} (G : SimpleGraph (GridVertex m n))
    [DecidableRel G.Adj] (hG : G ≤ gridGraph m n) :
    (∑ v ∈ gridWhite m n, G.degree v) = G.edgeFinset.card := by
  exact SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'
    (isBipartiteWith_checkerboard_of_le_gridGraph G hG)

/-- A `4 x n` spanning tree omits exactly `3(n-1)` grid edges. -/
theorem card_widthFour_cotree_edges {n : Nat} (hn : 1 ≤ n)
    {T : SimpleGraph (GridVertex 4 n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 4 n) T) :
    (gridGraph 4 n \ T).edgeFinset.card = 3 * (n - 1) := by
  have hsubset : T.edgeFinset ⊆ (gridGraph 4 n).edgeFinset := by
    exact SimpleGraph.edgeFinset_mono hT.le
  rw [SimpleGraph.edgeFinset_sdiff, Finset.card_sdiff_of_subset hsubset]
  have htree : T.edgeFinset.card + 1 = 4 * n := by
    convert hT.card_edgeFinset using 1;
      simp only [GridVertex, Fintype.card_prod, Fintype.card_fin]
  have hgrid : 2 * (gridGraph 4 n).edgeFinset.card = 2 * numEdges 4 n := by
    convert gridGraph_card_edgeFinset 4 n using 1
  have hgridCard : (gridGraph 4 n).edgeFinset.card = numEdges 4 n := by omega
  have htreeCard : T.edgeFinset.card = 4 * n - 1 := by omega
  rw [hgridCard, htreeCard]
  simp only [numEdges, numHoriz, numVert]
  omega

/-- The omitted-edge degree sum on each checkerboard color is `3(n-1)`. -/
theorem widthFour_cotree_color_degree_sums {n : Nat} (_hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex 4 n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 4 n) T) :
    (∑ v ∈ gridBlack 4 n, (gridGraph 4 n \ T).degree v) = 3 * (n - 1) ∧
      (∑ v ∈ gridWhite 4 n, (gridGraph 4 n \ T).degree v) = 3 * (n - 1) := by
  have hbip := isBipartiteWith_checkerboard_of_le_gridGraph
    (gridGraph 4 n \ T) (by exact sdiff_le)
  have hequal :
      (∑ v ∈ gridBlack 4 n, (gridGraph 4 n \ T).degree v) =
        ∑ v ∈ gridWhite 4 n, (gridGraph 4 n \ T).degree v := by
    exact SimpleGraph.isBipartiteWith_sum_degrees_eq hbip
  have hdisjoint := blackCenters_disjoint_whiteCenters
    (F := (Finset.univ : Finset (GridVertex 4 n)))
  have hBW : Disjoint (gridBlack 4 n) (gridWhite 4 n) := by
    simpa [blackCenters, whiteCenters] using hdisjoint
  have hsplit :
      (∑ v ∈ gridBlack 4 n, (gridGraph 4 n \ T).degree v) +
          ∑ v ∈ gridWhite 4 n, (gridGraph 4 n \ T).degree v =
        ∑ v : GridVertex 4 n, (gridGraph 4 n \ T).degree v := by
    rw [← Finset.sum_union hBW, gridBlack_union_gridWhite]
  have htotal : (∑ v : GridVertex 4 n, (gridGraph 4 n \ T).degree v) =
      D 4 n := by
    calc
      (∑ v : GridVertex 4 n, (gridGraph 4 n \ T).degree v) =
          ∑ v : GridVertex 4 n, vertexDeficiency 4 n T v := by
            apply Finset.sum_congr rfl
            intro v _
            exact grid_cotree_degree_eq_vertexDeficiency hT.le v
      _ = D 4 n := total_deficiency hT
  have hvalue : D 4 n = 6 * (n - 1) := by
    unfold D
    omega
  rw [hvalue] at htotal
  constructor <;> omega

/-- Exact colorwise waste ledger on the black checkerboard class. -/
theorem widthFour_black_waste_ledger {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex 4 n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 4 n) T) :
    incidenceWasteOn (gridGraph 4 n \ T) (gridBlack 4 n) + 3 * (n - 1) =
      3 * (supportFinset (gridGraph 4 n \ T) ∩ gridBlack 4 n).card := by
  let D := gridGraph 4 n \ T
  change incidenceWasteOn D (gridBlack 4 n) + 3 * (n - 1) =
    3 * (supportFinset D ∩ gridBlack 4 n).card
  have hledger := incidenceWasteOn_add_degreeSum
    D (gridBlack 4 n)
    (grid_cotree_degree_le_three (by omega) hn hT)
  rw [sum_degrees_support_inter_eq] at hledger
  have hcolor := (widthFour_cotree_color_degree_sums hn hT).1
  change (∑ v ∈ gridBlack 4 n, D.degree v) = 3 * (n - 1) at hcolor
  omega

/-- Exact colorwise waste ledger on the white checkerboard class. -/
theorem widthFour_white_waste_ledger {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex 4 n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 4 n) T) :
    incidenceWasteOn (gridGraph 4 n \ T) (gridWhite 4 n) + 3 * (n - 1) =
      3 * (supportFinset (gridGraph 4 n \ T) ∩ gridWhite 4 n).card := by
  let D := gridGraph 4 n \ T
  change incidenceWasteOn D (gridWhite 4 n) + 3 * (n - 1) =
    3 * (supportFinset D ∩ gridWhite 4 n).card
  have hledger := incidenceWasteOn_add_degreeSum
    D (gridWhite 4 n)
    (grid_cotree_degree_le_three (by omega) hn hT)
  rw [sum_degrees_support_inter_eq] at hledger
  have hcolor := (widthFour_cotree_color_degree_sums hn hT).2
  change (∑ v ∈ gridWhite 4 n, D.degree v) = 3 * (n - 1) at hcolor
  omega

/-! ## The rectangular perimeter cycle -/

private def widthFourPerimeterVertex {n : Nat} (hn : 2 ≤ n)
    (i : Fin (2 * n + 4)) :
    GridVertex 4 n :=
  if htop : i.val < n then
    (⟨0, by omega⟩, ⟨i.val, htop⟩)
  else if hright : i.val < n + 3 then
    (⟨i.val - n + 1, by omega⟩, ⟨n - 1, by omega⟩)
  else if hbottom : i.val < 2 * n + 2 then
    (⟨3, by omega⟩, ⟨2 * n + 1 - i.val, by omega⟩)
  else
    (⟨2 * n + 4 - i.val, by omega⟩, ⟨0, by omega⟩)

private def widthFourPerimeterIndex (n : Nat) (v : GridVertex 4 n) : Nat :=
  if v.1.val = 0 then v.2.val
  else if v.2.val + 1 = n then n + v.1.val - 1
  else if v.1.val = 3 then 2 * n + 1 - v.2.val
  else 2 * n + 4 - v.1.val

private theorem widthFourPerimeterIndex_vertex {n : Nat} (hn : 2 ≤ n)
    (i : Fin (2 * n + 4)) :
    widthFourPerimeterIndex n (widthFourPerimeterVertex hn i) = i.val := by
  unfold widthFourPerimeterIndex widthFourPerimeterVertex
  split_ifs <;> simp_all <;> omega

private theorem widthFourPerimeterVertex_injective {n : Nat} (hn : 2 ≤ n) :
    Function.Injective (widthFourPerimeterVertex hn) := by
  intro i j hij
  apply Fin.ext
  rw [← widthFourPerimeterIndex_vertex hn i,
    ← widthFourPerimeterIndex_vertex hn j, hij]

private theorem widthFourPerimeterVertex_boundary {n : Nat} (hn : 2 ≤ n)
    (i : Fin (2 * n + 4)) :
    IsGridBoundary (widthFourPerimeterVertex hn i) := by
  unfold widthFourPerimeterVertex IsGridBoundary
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr (Or.inr (by simp; omega)))
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))

private theorem widthFourPerimeterVertex_top {n : Nat} (hn : 2 ≤ n)
    (i : Fin (2 * n + 4)) (hi : i.val < n) :
    widthFourPerimeterVertex hn i =
      (⟨0, by omega⟩, ⟨i.val, hi⟩) := by
  simp [widthFourPerimeterVertex, hi]

private theorem widthFourPerimeterVertex_right {n : Nat} (hn : 2 ≤ n)
    (i : Fin (2 * n + 4)) (htop : ¬i.val < n) (hi : i.val < n + 3) :
    widthFourPerimeterVertex hn i =
      (⟨i.val - n + 1, by omega⟩, ⟨n - 1, by omega⟩) := by
  simp [widthFourPerimeterVertex, htop, hi]

private theorem widthFourPerimeterVertex_bottom {n : Nat} (hn : 2 ≤ n)
    (i : Fin (2 * n + 4)) (hright : ¬i.val < n + 3)
    (hi : i.val < 2 * n + 2) :
    widthFourPerimeterVertex hn i =
      (⟨3, by omega⟩, ⟨2 * n + 1 - i.val, by omega⟩) := by
  have htop : ¬i.val < n := by omega
  simp [widthFourPerimeterVertex, htop, hright, hi]

private theorem widthFourPerimeterVertex_left {n : Nat} (hn : 2 ≤ n)
    (i : Fin (2 * n + 4)) (hi : ¬i.val < 2 * n + 2) :
    widthFourPerimeterVertex hn i =
      (⟨2 * n + 4 - i.val, by omega⟩, ⟨0, by omega⟩) := by
  have htop : ¬i.val < n := by omega
  have hright : ¬i.val < n + 3 := by omega
  simp [widthFourPerimeterVertex, htop, hright, hi]

private theorem widthFourPerimeterVertex_succ_adj {n : Nat} (hn : 2 ≤ n)
    (i : Fin (2 * n + 4)) :
    (gridGraph 4 n).Adj (widthFourPerimeterVertex hn i)
      (widthFourPerimeterVertex hn (i + 1)) := by
  by_cases hi : i.val + 1 < 2 * n + 4
  · have hval : (i + 1).val = i.val + 1 := by
      simp only [Fin.val_add, Fin.val_one]
      exact Nat.mod_eq_of_lt hi
    have heq : i + 1 = ⟨i.val + 1, hi⟩ := Fin.ext hval
    rw [heq]
    by_cases htop : i.val < n
    · by_cases hnext : i.val + 1 < n
      · rw [widthFourPerimeterVertex_top hn i htop,
          widthFourPerimeterVertex_top hn ⟨i.val + 1, hi⟩ hnext]
        left
        exact ⟨rfl, Or.inl rfl⟩
      · have hieq : i.val = n - 1 := by omega
        have hnextRight : i.val + 1 < n + 3 := by omega
        rw [widthFourPerimeterVertex_top hn i htop,
          widthFourPerimeterVertex_right hn ⟨i.val + 1, hi⟩ hnext hnextRight]
        right
        constructor
        · apply Fin.ext
          simp
          omega
        · exact Or.inl (by simp; omega)
    · by_cases hright : i.val < n + 3
      · by_cases hnext : i.val + 1 < n + 3
        · have hnextTop : ¬i.val + 1 < n := by omega
          rw [widthFourPerimeterVertex_right hn i htop hright,
            widthFourPerimeterVertex_right hn ⟨i.val + 1, hi⟩ hnextTop hnext]
          right
          exact ⟨rfl, Or.inl (by simp; omega)⟩
        · have hieq : i.val = n + 2 := by omega
          have hnextBottom : i.val + 1 < 2 * n + 2 := by omega
          rw [widthFourPerimeterVertex_right hn i htop hright,
            widthFourPerimeterVertex_bottom hn ⟨i.val + 1, hi⟩ hnext hnextBottom]
          left
          constructor
          · apply Fin.ext
            simp
            omega
          · exact Or.inr (by simp; omega)
      · by_cases hbottom : i.val < 2 * n + 2
        · by_cases hnext : i.val + 1 < 2 * n + 2
          · rw [widthFourPerimeterVertex_bottom hn i hright hbottom,
              widthFourPerimeterVertex_bottom hn ⟨i.val + 1, hi⟩
                (by omega) hnext]
            left
            exact ⟨rfl, Or.inr (by simp; omega)⟩
          · have hieq : i.val = 2 * n + 1 := by omega
            rw [widthFourPerimeterVertex_bottom hn i hright hbottom,
              widthFourPerimeterVertex_left hn ⟨i.val + 1, hi⟩ hnext]
            right
            exact ⟨by apply Fin.ext; simp; omega, Or.inr (by simp; omega)⟩
        · have hnextTop : ¬i.val + 1 < n := by omega
          have hnextRight : ¬i.val + 1 < n + 3 := by omega
          have hnextBottom : ¬i.val + 1 < 2 * n + 2 := by omega
          rw [widthFourPerimeterVertex_left hn i hbottom,
            widthFourPerimeterVertex_left hn ⟨i.val + 1, hi⟩ hnextBottom]
          right
          exact ⟨by apply Fin.ext; rfl, Or.inr (by simp; omega)⟩
  · have hilast : i.val + 1 = 2 * n + 4 := by omega
    have hval : (i + 1).val = 0 := by
      simp only [Fin.val_add, Fin.val_one, hilast, Nat.mod_self]
    have heq : i + 1 = ⟨0, by omega⟩ := Fin.ext hval
    rw [heq]
    have hiV : widthFourPerimeterVertex hn i =
        (⟨1, by omega⟩, ⟨0, by omega⟩) := by
      unfold widthFourPerimeterVertex
      split_ifs <;> apply Prod.ext <;> apply Fin.ext <;> simp_all <;> omega
    have hzV : widthFourPerimeterVertex hn
        (⟨0, by positivity⟩ : Fin (2 * n + 4)) =
        (⟨0, by omega⟩, ⟨0, by omega⟩) := by
      unfold widthFourPerimeterVertex
      rw [dif_pos (show 0 < n by omega)]
    rw [hiV, hzV]
    right
    exact ⟨rfl, Or.inr rfl⟩

private def widthFourPerimeterHom {n : Nat} (hn : 2 ≤ n) :
    cycleGraph (2 * n + 4) →g gridGraph 4 n where
  toFun := widthFourPerimeterVertex hn
  map_rel' := by
    intro i j hij
    have hj : j = i - 1 ∨ j = i + 1 := by
      have hjmem : j ∈ (cycleGraph (2 * n + 4)).neighborSet i := hij
      rw [cycleGraph_neighborSet] at hjmem
      simpa [eq_comm] using hjmem
    rcases hj with h | h
    · have hi : i = j + 1 := by
        rw [h]
        simp
      rw [hi]
      exact (widthFourPerimeterVertex_succ_adj hn j).symm
    · rw [h]
      exact widthFourPerimeterVertex_succ_adj hn i

private theorem cycleGraph_two_mul_add_four_not_isAcyclic {n : Nat} :
    ¬(cycleGraph (2 * n + 4)).IsAcyclic := by
  intro hacyc
  have htree : (cycleGraph (2 * n + 4)).IsTree :=
    ⟨cycleGraph_connected, hacyc⟩
  have hcard := htree.card_edgeFinset
  have hdeg := (cycleGraph (2 * n + 4)).sum_degrees_eq_twice_card_edges
  have htwo : ∀ i : Fin (2 * n + 4),
      (cycleGraph (2 * n + 4)).degree i = 2 := by
    intro i
    exact cycleGraph_degree_three_le
  rw [Finset.sum_congr rfl (fun i _ => htwo i)] at hdeg
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hdeg
  simp only [Fintype.card_fin] at hcard
  omega

/-- Every `4 x n` spanning tree omits an edge of the outer perimeter. -/
theorem exists_omitted_widthFour_perimeter_edge {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex 4 n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 4 n) T) :
    ∃ u v, (gridGraph 4 n).Adj u v ∧ IsGridBoundary u ∧
      IsGridBoundary v ∧ ¬T.Adj u v := by
  by_contra hnone
  push Not at hnone
  let hemb : cycleGraph (2 * n + 4) →g T :=
    { toFun := widthFourPerimeterVertex hn
      map_rel' := by
        intro i j hij
        have hgrid := (widthFourPerimeterHom hn).map_rel hij
        apply hnone (widthFourPerimeterVertex hn i)
          (widthFourPerimeterVertex hn j) hgrid
        · exact widthFourPerimeterVertex_boundary hn i
        · exact widthFourPerimeterVertex_boundary hn j }
  have hinj : Function.Injective hemb := by
    intro i j hij
    exact widthFourPerimeterVertex_injective hn hij
  exact cycleGraph_two_mul_add_four_not_isAcyclic
    (hT.isAcyclic.comap hemb hinj)

/-- Each endpoint of an omitted perimeter edge has positive local waste. -/
theorem omitted_widthFour_perimeter_endpoint_waste {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex 4 n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 4 n) T)
    {u v : GridVertex 4 n} (_huv : (gridGraph 4 n).Adj u v)
    (hu : IsGridBoundary u) (hv : IsGridBoundary v) (_hnot : ¬T.Adj u v) :
    1 ≤ 3 - (gridGraph 4 n \ T).degree u ∧
      1 ≤ 3 - (gridGraph 4 n \ T).degree v := by
  have endpoint (x : GridVertex 4 n) (hx : IsGridBoundary x) :
      1 ≤ 3 - (gridGraph 4 n \ T).degree x := by
    rw [degree_sdiff_of_le (gridGraph 4 n) T hT.le]
    have hboundary := one_le_gridBoundaryDeficiency_of_boundary
      (by omega : 2 ≤ 4) hn x hx
    have htree := tree_degree_pos (by nlinarith [hn]) hT x
    unfold gridBoundaryDeficiency at hboundary
    omega
  exact ⟨endpoint u hu, endpoint v hv⟩

theorem one_le_incidenceWasteOn_of_mem {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) {v : V} (hv : v ∈ supportFinset G ∩ C)
    (hwaste : 1 ≤ 3 - G.degree v) :
    1 ≤ incidenceWasteOn G C := by
  unfold incidenceWasteOn
  calc
    1 ≤ ∑ x ∈ ({v} : Finset V), (3 - G.degree x) := by simp [hwaste]
    _ ≤ ∑ x ∈ supportFinset G ∩ C, (3 - G.degree x) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa using hv
      · simp

/-- The omitted perimeter edge makes both checkerboard color wastes positive. -/
theorem widthFour_color_wastes_positive {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex 4 n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 4 n) T) :
    1 ≤ incidenceWasteOn (gridGraph 4 n \ T) (gridBlack 4 n) ∧
      1 ≤ incidenceWasteOn (gridGraph 4 n \ T) (gridWhite 4 n) := by
  obtain ⟨u, v, huv, hu, hv, hnot⟩ :=
    exists_omitted_widthFour_perimeter_edge hn hT
  have hcotree : (gridGraph 4 n \ T).Adj u v := ⟨huv, hnot⟩
  have hwaste := omitted_widthFour_perimeter_endpoint_waste
    hn hT huv hu hv hnot
  have huSupport : u ∈ supportFinset (gridGraph 4 n \ T) := by
    rw [mem_supportFinset, SimpleGraph.degree_pos_iff_mem_support]
    exact ⟨v, hcotree⟩
  have hvSupport : v ∈ supportFinset (gridGraph 4 n \ T) := by
    rw [mem_supportFinset, SimpleGraph.degree_pos_iff_mem_support]
    exact ⟨u, hcotree.symm⟩
  rcases (gridGraph_isBipartiteWith_checkerboard 4 n).mem_of_adj huv with
    ⟨huBlack, hvWhite⟩ | ⟨huWhite, hvBlack⟩
  · exact ⟨one_le_incidenceWasteOn_of_mem _ _
      (Finset.mem_inter.mpr ⟨huSupport, huBlack⟩) hwaste.1,
      one_le_incidenceWasteOn_of_mem _ _
      (Finset.mem_inter.mpr ⟨hvSupport, hvWhite⟩) hwaste.2⟩
  · exact ⟨one_le_incidenceWasteOn_of_mem _ _
      (Finset.mem_inter.mpr ⟨hvSupport, hvBlack⟩) hwaste.2,
      one_le_incidenceWasteOn_of_mem _ _
      (Finset.mem_inter.mpr ⟨huSupport, huWhite⟩) hwaste.1⟩

/-- Every `4 x n` spanning tree has at most `2n` full-degree vertices. -/
theorem widthFour_numPreserved_le_two_mul {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex 4 n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 4 n) T) :
    numPreserved 4 n T ≤ 2 * n := by
  let U := supportFinset (gridGraph 4 n \ T)
  let UB := U ∩ gridBlack 4 n
  let UW := U ∩ gridWhite 4 n
  have hpositive := widthFour_color_wastes_positive hn hT
  have hblackLedger := widthFour_black_waste_ledger hn hT
  have hwhiteLedger := widthFour_white_waste_ledger hn hT
  have hnBlack : n ≤ UB.card := by
    dsimp only [UB, U]
    omega
  have hnWhite : n ≤ UW.card := by
    dsimp only [UW, U]
    omega
  have hBW : Disjoint (gridBlack 4 n) (gridWhite 4 n) := by
    rw [Finset.disjoint_left]
    intro v hvBlack hvWhite
    exact (Finset.mem_sdiff.mp hvWhite).2 hvBlack
  have hdisjoint : Disjoint UB UW :=
    Finset.disjoint_left.mpr fun v hvB hvW =>
      (Finset.disjoint_left.mp hBW) (Finset.mem_inter.mp hvB).2
        (Finset.mem_inter.mp hvW).2
  have hunion : UB ∪ UW = U := by
    dsimp only [UB, UW]
    rw [← Finset.inter_union_distrib_left, gridBlack_union_gridWhite]
    simp
  have hcard := Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hcard
  have hsupport := grid_cotree_support_card_add_numPreserved hT.le
  change U.card + numPreserved 4 n T = 4 * n at hsupport
  omega

/-- Operational width-four upper bound. -/
theorem maxPreserved_widthFour_le_two_mul {n : Nat} (hn : 2 ≤ n) :
    maxPreserved 4 n ≤ 2 * n := by
  apply maxPreserved_le_of_forall
  intro T _ hT
  exact widthFour_numPreserved_le_two_mul hn hT

/-- Exact full-degree spanning-tree maximum on every nondegenerate `4 x n`
grid. -/
theorem maxPreserved_widthFour_eq_two_mul {n : Nat} (hn : 2 ≤ n) :
    maxPreserved 4 n = 2 * n :=
  Nat.le_antisymm (maxPreserved_widthFour_le_two_mul hn)
    (two_mul_le_maxPreserved_widthFour hn)

/-- Exact forced-forest maximum on the same family. -/
theorem maxForcedAcyclic_widthFour_eq_two_mul {n : Nat} (hn : 2 ≤ n) :
    maxForcedAcyclic 4 n = 2 * n := by
  rw [← maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  exact maxPreserved_widthFour_eq_two_mul hn

end GridGraphs
