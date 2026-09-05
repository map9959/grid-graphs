import GridGraphs.WidthFourExact

/-!
# Checkerboard splitting of square-grid cotree waste

The cotree of a square-grid spanning tree has the same degree sum on each
checkerboard class.  This gives exact colorwise waste ledgers and, in the
residue-two family, arithmetic normal forms for equality and near-equality
waste levels.  The final results are consequences of the stated equalities;
they make no nonexistence claim.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- A spanning tree of the `n x n` grid omits exactly `(n - 1)^2` edges. -/
theorem card_square_cotree_edges {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    (gridGraph n n \ T).edgeFinset.card = (n - 1) ^ 2 := by
  have hsubset : T.edgeFinset ⊆ (gridGraph n n).edgeFinset :=
    SimpleGraph.edgeFinset_mono hT.le
  have hcardle := Finset.card_le_card hsubset
  rw [SimpleGraph.edgeFinset_sdiff, Finset.card_sdiff_of_subset hsubset]
  have htree : T.edgeFinset.card + 1 = n * n := by
    convert hT.card_edgeFinset using 1
    simp only [GridVertex, Fintype.card_prod, Fintype.card_fin]
  have hgrid : (gridGraph n n).edgeFinset.card = numEdges n n := by
    have h := gridGraph_card_edgeFinset n n
    omega
  rw [hgrid] at hcardle ⊢
  have hn : 1 ≤ n := by
    by_contra hn
    have : n = 0 := by omega
    simp [this] at htree
  have hsub : n - 1 + 1 = n := by omega
  simp only [numEdges, numHoriz, numVert, pow_two] at hcardle ⊢
  rw [Nat.sub_eq_iff_eq_add hcardle]
  nlinarith

/-- Each checkerboard class has one cotree incidence for every omitted edge. -/
theorem square_cotree_color_degree_sums {n : Nat}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    (∑ v ∈ gridBlack n n, (gridGraph n n \ T).degree v) = (n - 1) ^ 2 ∧
      (∑ v ∈ gridWhite n n, (gridGraph n n \ T).degree v) = (n - 1) ^ 2 := by
  let G := gridGraph n n \ T
  have hequal : (∑ v ∈ gridBlack n n, G.degree v) =
      ∑ v ∈ gridWhite n n, G.degree v :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq
      (isBipartiteWith_checkerboard_of_le_gridGraph G (by exact sdiff_le))
  have hdisjoint : Disjoint (gridBlack n n) (gridWhite n n) := by
    simpa [blackCenters, whiteCenters] using
      blackCenters_disjoint_whiteCenters
        (F := (Finset.univ : Finset (GridVertex n n)))
  have hsplit :
      (∑ v ∈ gridBlack n n, G.degree v) +
          ∑ v ∈ gridWhite n n, G.degree v =
        ∑ v : GridVertex n n, G.degree v := by
    rw [← Finset.sum_union hdisjoint, gridBlack_union_gridWhite]
  have htotal : (∑ v : GridVertex n n, G.degree v) = D n n := by
    change (∑ v : GridVertex n n, (gridGraph n n \ T).degree v) = D n n
    calc
      (∑ v : GridVertex n n, (gridGraph n n \ T).degree v) =
          ∑ v : GridVertex n n, vertexDeficiency n n T v := by
            apply Finset.sum_congr rfl
            intro v _
            exact grid_cotree_degree_eq_vertexDeficiency hT.le v
      _ = D n n := total_deficiency hT
  have hvalue : D n n = 2 * (n - 1) ^ 2 := by
    simp only [D, pow_two, Nat.mul_assoc]
  change
    (∑ v ∈ gridBlack n n, G.degree v) = (n - 1) ^ 2 ∧
      (∑ v ∈ gridWhite n n, G.degree v) = (n - 1) ^ 2
  rw [hvalue] at htotal
  constructor <;> omega

/-- Exact cotree waste ledger on the black checkerboard class. -/
theorem square_cotree_black_waste_ledger {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    incidenceWasteOn (gridGraph n n \ T) (gridBlack n n) + (n - 1) ^ 2 =
      3 * (supportFinset (gridGraph n n \ T) ∩ gridBlack n n).card := by
  have hledger := incidenceWasteOn_add_degreeSum
    (gridGraph n n \ T) (gridBlack n n)
    (grid_cotree_degree_le_three hn hn hT)
  rw [sum_degrees_support_inter_eq,
    (square_cotree_color_degree_sums hT).1] at hledger
  exact hledger

/-- Exact cotree waste ledger on the white checkerboard class. -/
theorem square_cotree_white_waste_ledger {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    incidenceWasteOn (gridGraph n n \ T) (gridWhite n n) + (n - 1) ^ 2 =
      3 * (supportFinset (gridGraph n n \ T) ∩ gridWhite n n).card := by
  have hledger := incidenceWasteOn_add_degreeSum
    (gridGraph n n \ T) (gridWhite n n)
    (grid_cotree_degree_le_three hn hn hT)
  rw [sum_degrees_support_inter_eq,
    (square_cotree_color_degree_sums hT).2] at hledger
  exact hledger

/-- Incidence waste splits exactly into its black and white contributions. -/
theorem grid_incidenceWaste_eq_black_add_white {m n : Nat}
    (G : SimpleGraph (GridVertex m n)) [DecidableRel G.Adj] :
    incidenceWaste G =
      incidenceWasteOn G (gridBlack m n) +
        incidenceWasteOn G (gridWhite m n) := by
  unfold incidenceWaste incidenceWasteOn
  have hdisjoint : Disjoint
      (supportFinset G ∩ gridBlack m n)
      (supportFinset G ∩ gridWhite m n) := by
    apply Finset.disjoint_left.mpr
    intro v hvB hvW
    exact (gridGraph_isBipartiteWith_checkerboard m n).disjoint.le_bot
      ⟨(Finset.mem_inter.mp hvB).2, (Finset.mem_inter.mp hvW).2⟩
  rw [← Finset.sum_union hdisjoint]
  congr 1
  rw [← Finset.inter_union_distrib_left, gridBlack_union_gridWhite]
  simp

/-- Two nonnegative three-unit surpluses with total surplus zero both vanish. -/
theorem three_mul_surpluses_eq_zero {b w : Nat}
    (h : 3 * b + 3 * w = 0) :
    b = 0 ∧ w = 0 := by
  omega

/-- Two nonnegative three-unit surpluses with total surplus three consist of
exactly one packet, carried by exactly one of the two terms. -/
theorem three_mul_surpluses_eq_three {b w : Nat}
    (h : 3 * b + 3 * w = 3) :
    (b = 1 ∧ w = 0) ∨ (b = 0 ∧ w = 1) := by
  omega

/-- Under `W = n + 2` in the residue-two family, both color wastes are two
modulo three, and their quotients sum to `k`. -/
theorem residueTwo_color_waste_normal_form {k : Nat}
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree
      (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (heq : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 2) :
    ∃ b w : Nat,
      incidenceWasteOn
          (gridGraph (3 * k + 2) (3 * k + 2) \ T)
          (gridBlack (3 * k + 2) (3 * k + 2)) = 3 * b + 2 ∧
      incidenceWasteOn
          (gridGraph (3 * k + 2) (3 * k + 2) \ T)
          (gridWhite (3 * k + 2) (3 * k + 2)) = 3 * w + 2 ∧
      b + w = k := by
  have hblack := square_cotree_black_waste_ledger (n := 3 * k + 2) (by omega) hT
  have hwhite := square_cotree_white_waste_ledger (n := 3 * k + 2) (by omega) hT
  have hsplit := grid_incidenceWaste_eq_black_add_white
    (gridGraph (3 * k + 2) (3 * k + 2) \ T)
  have hsquare : (3 * k + 2 - 1) ^ 2 =
      3 * (3 * k ^ 2 + 2 * k) + 1 := by
    have hsub : 3 * k + 2 - 1 = 3 * k + 1 := by omega
    rw [hsub]
    ring
  rw [hsquare] at hblack hwhite
  rw [hsplit] at heq
  let q := 3 * k ^ 2 + 2 * k
  let b := (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T) ∩
    gridBlack (3 * k + 2) (3 * k + 2)).card - q - 1
  let w := (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T) ∩
    gridWhite (3 * k + 2) (3 * k + 2)).card - q - 1
  refine ⟨b, w, ?_, ?_, ?_⟩ <;> dsimp only [b, w, q]
  · omega
  · omega
  · omega

/-- Under `W = n + 5` in the residue-two family, both color wastes retain the
same residue, and their quotients sum to `k + 1`. -/
theorem residueTwo_near_color_waste_normal_form {k : Nat}
    {T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2))}
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree
      (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (heq : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 5) :
    ∃ b w : Nat,
      incidenceWasteOn
          (gridGraph (3 * k + 2) (3 * k + 2) \ T)
          (gridBlack (3 * k + 2) (3 * k + 2)) = 3 * b + 2 ∧
      incidenceWasteOn
          (gridGraph (3 * k + 2) (3 * k + 2) \ T)
          (gridWhite (3 * k + 2) (3 * k + 2)) = 3 * w + 2 ∧
      b + w = k + 1 := by
  have hblack := square_cotree_black_waste_ledger (n := 3 * k + 2) (by omega) hT
  have hwhite := square_cotree_white_waste_ledger (n := 3 * k + 2) (by omega) hT
  have hsplit := grid_incidenceWaste_eq_black_add_white
    (gridGraph (3 * k + 2) (3 * k + 2) \ T)
  have hsquare : (3 * k + 2 - 1) ^ 2 =
      3 * (3 * k ^ 2 + 2 * k) + 1 := by
    have hsub : 3 * k + 2 - 1 = 3 * k + 1 := by omega
    rw [hsub]
    ring
  rw [hsquare] at hblack hwhite
  rw [hsplit] at heq
  let q := 3 * k ^ 2 + 2 * k
  let b := (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T) ∩
    gridBlack (3 * k + 2) (3 * k + 2)).card - q - 1
  let w := (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T) ∩
    gridWhite (3 * k + 2) (3 * k + 2)).card - q - 1
  refine ⟨b, w, ?_, ?_, ?_⟩ <;> dsimp only [b, w, q]
  · omega
  · omega
  · omega

/-- In the `k = 0` tight normal form, both checkerboard classes have waste
exactly two. -/
theorem residueTwo_tight_color_wastes_of_k_zero
    {T : SimpleGraph (GridVertex 2 2)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 2 2) T)
    (heq : incidenceWaste (gridGraph 2 2 \ T) = 2 + 2) :
    incidenceWasteOn (gridGraph 2 2 \ T) (gridBlack 2 2) = 2 ∧
      incidenceWasteOn (gridGraph 2 2 \ T) (gridWhite 2 2) = 2 := by
  obtain ⟨b, w, hblack, hwhite, hsum⟩ :=
    residueTwo_color_waste_normal_form (k := 0) hT heq
  have hsurplus : 3 * b + 3 * w = 0 := by omega
  obtain ⟨rfl, rfl⟩ := three_mul_surpluses_eq_zero hsurplus
  exact ⟨by simpa using hblack, by simpa using hwhite⟩

/-- In the `k = 0` near normal form, exactly one checkerboard class carries
the single additional three-unit waste packet. -/
theorem residueTwo_near_color_wastes_of_k_zero
    {T : SimpleGraph (GridVertex 2 2)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 2 2) T)
    (heq : incidenceWaste (gridGraph 2 2 \ T) = 2 + 5) :
    (incidenceWasteOn (gridGraph 2 2 \ T) (gridBlack 2 2) = 5 ∧
        incidenceWasteOn (gridGraph 2 2 \ T) (gridWhite 2 2) = 2) ∨
      (incidenceWasteOn (gridGraph 2 2 \ T) (gridBlack 2 2) = 2 ∧
        incidenceWasteOn (gridGraph 2 2 \ T) (gridWhite 2 2) = 5) := by
  obtain ⟨b, w, hblack, hwhite, hsum⟩ :=
    residueTwo_near_color_waste_normal_form (k := 0) hT heq
  have hsurplus : 3 * b + 3 * w = 3 := by omega
  rcases three_mul_surpluses_eq_three hsurplus with hbw | hbw
  · obtain ⟨rfl, rfl⟩ := hbw
    exact Or.inl ⟨by simpa using hblack, by simpa using hwhite⟩
  · obtain ⟨rfl, rfl⟩ := hbw
    exact Or.inr ⟨by simpa using hblack, by simpa using hwhite⟩

end GridGraphs
