import GridGraphs.CotreeWaste
import GridGraphs.MaxPreserved

/-!
# Elementary perimeter incidence-waste bounds

The outer boundary of a nondegenerate square grid is a cycle.  A spanning
tree therefore omits one of its edges.  Both endpoints of such an edge are
boundary vertices, so their cotree degrees are at most two and each contributes
at least one unit of incidence waste.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- A vertex lies on the outer boundary of a square grid. -/
def IsBoundaryVertex (n : Nat) (v : GridVertex n n) : Prop :=
  v.1.val = 0 ∨ v.1.val + 1 = n ∨ v.2.val = 0 ∨ v.2.val + 1 = n

/-- An edge of the grid whose two endpoints lie on the outer boundary. -/
def IsPerimeterEdge (n : Nat) (u v : GridVertex n n) : Prop :=
  (gridGraph n n).Adj u v ∧ IsBoundaryVertex n u ∧ IsBoundaryVertex n v

private def perimeterVertex (k : Nat) (i : Fin ((4 * k - 2) + 2)) :
    GridVertex (k + 1) (k + 1) :=
  if h₁ : i.val < k then
    (⟨0, by omega⟩, ⟨i.val, by omega⟩)
  else if h₂ : i.val < 2 * k then
    (⟨i.val - k, by omega⟩, ⟨k, by omega⟩)
  else if h₃ : i.val < 3 * k then
    (⟨k, by omega⟩, ⟨3 * k - i.val, by omega⟩)
  else
    (⟨4 * k - i.val, by omega⟩, ⟨0, by omega⟩)

private def perimeterIndex (k : Nat) (v : GridVertex (k + 1) (k + 1)) : Nat :=
  if v.1.val = 0 then v.2.val
  else if v.2.val = k then k + v.1.val
  else if v.1.val = k then 3 * k - v.2.val
  else 4 * k - v.1.val

private lemma perimeterIndex_vertex {k : Nat} (hk : 1 ≤ k)
    (i : Fin ((4 * k - 2) + 2)) :
    perimeterIndex k (perimeterVertex k i) = i.val := by
  unfold perimeterIndex perimeterVertex
  split_ifs <;> simp_all <;> omega

private lemma perimeterVertex_injective {k : Nat} (hk : 1 ≤ k) :
    Function.Injective (perimeterVertex k) := by
  intro i j hij
  apply Fin.ext
  rw [← perimeterIndex_vertex hk i, ← perimeterIndex_vertex hk j, hij]

private lemma perimeterVertex_succ_adj {k : Nat} (hk : 1 ≤ k)
    (i : Fin ((4 * k - 2) + 2)) :
    (gridGraph (k + 1) (k + 1)).Adj (perimeterVertex k i)
      (perimeterVertex k (i + 1)) := by
  by_cases hi : i.val + 1 < 4 * k
  · have hval : (i + 1).val = i.val + 1 := by
      simp only [Fin.val_add, Fin.val_one]
      exact Nat.mod_eq_of_lt (by omega)
    have heq : i + 1 = ⟨i.val + 1, by omega⟩ := Fin.ext hval
    rw [heq]
    unfold perimeterVertex
    split_ifs <;> simp_all [gridGraph, adjacent] <;> norm_num at * <;> omega
  · have hilast : i.val + 1 = 4 * k := by omega
    have hval : (i + 1).val = 0 := by
      simp only [Fin.val_add, Fin.val_one, hilast]
      have hN : 4 * k - 2 + 2 = 4 * k := by omega
      rw [hN, Nat.mod_self]
    have heq : i + 1 = ⟨0, by omega⟩ := Fin.ext hval
    rw [heq]
    have hiV : perimeterVertex k i =
        (⟨1, by omega⟩, ⟨0, by omega⟩) := by
      unfold perimeterVertex
      split_ifs <;> apply Prod.ext <;> apply Fin.ext <;> simp_all <;> omega
    have hzV : perimeterVertex k (⟨0, by omega⟩ : Fin ((4 * k - 2) + 2)) =
        (⟨0, by omega⟩, ⟨0, by omega⟩) := by
      unfold perimeterVertex
      rw [dif_pos (by simpa using hk : (⟨0, by omega⟩ :
        Fin ((4 * k - 2) + 2)).val < k)]
    rw [hiV, hzV]
    right
    exact ⟨rfl, Or.inr rfl⟩

private def perimeterHom {k : Nat} (hk : 1 ≤ k) :
    cycleGraph ((4 * k - 2) + 2) →g gridGraph (k + 1) (k + 1) where
  toFun := perimeterVertex k
  map_rel' := by
    intro i j hij
    have hj : j = i - 1 ∨ j = i + 1 := by
      have hjmem : j ∈ (cycleGraph ((4 * k - 2) + 2)).neighborSet i := hij
      rw [cycleGraph_neighborSet] at hjmem
      simpa [eq_comm] using hjmem
    rcases hj with h | h
    · have hi : i = j + 1 := by
        rw [h]
        simp
      rw [hi]
      exact (perimeterVertex_succ_adj hk j).symm
    · rw [h]
      exact perimeterVertex_succ_adj hk i

private lemma cycleGraph_four_mul_not_isAcyclic {k : Nat} (hk : 1 ≤ k) :
    ¬(cycleGraph ((4 * k - 2) + 2)).IsAcyclic := by
  intro hacyc
  have hconn : (cycleGraph ((4 * k - 2) + 2)).Connected :=
    cycleGraph_connected
  have htree : (cycleGraph ((4 * k - 2) + 2)).IsTree := ⟨hconn, hacyc⟩
  have hcard := htree.card_edgeFinset
  have hdeg := (cycleGraph ((4 * k - 2) + 2)).sum_degrees_eq_twice_card_edges
  have htwo : ∀ i : Fin ((4 * k - 2) + 2),
      (cycleGraph ((4 * k - 2) + 2)).degree i = 2 := by
    intro i
    rw [cycleGraph_degree_two_le, Finset.card_pair]
    intro heq
    have hi : i = i + 2 := by
      have := congrArg (fun x => x + 1) heq
      simpa [sub_eq_add_neg, add_assoc] using this
    have hzero : (0 : Fin ((4 * k - 2) + 2)) = 2 := by
      exact add_left_cancel (a := i) (by simpa using hi)
    have := congrArg Fin.val hzero
    have h2lt : 2 < 4 * k - 2 + 2 := by omega
    have htwoVal : (2 : Fin ((4 * k - 2) + 2)).val = 2 :=
      Nat.mod_eq_of_lt h2lt
    rw [htwoVal] at this
    simp only [Fin.val_zero] at this
    omega
  rw [Finset.sum_congr rfl (fun i _ => htwo i)] at hdeg
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hdeg
  simp only [Fintype.card_fin] at hcard
  omega

/-- Every spanning subtree of a nondegenerate square omits a perimeter edge. -/
theorem exists_omitted_perimeter_edge {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    ∃ u v, IsPerimeterEdge n u v ∧ ¬T.Adj u v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hk : 1 ≤ k := by omega
  by_contra hnone
  push_neg at hnone
  let hemb : cycleGraph ((4 * k - 2) + 2) →g T :=
    { toFun := perimeterVertex k
      map_rel' := by
        intro i j hij
        have hgrid := (perimeterHom hk).map_rel hij
        apply hnone (perimeterVertex k i) (perimeterVertex k j)
        refine ⟨hgrid, ?_, ?_⟩
        all_goals
          unfold IsBoundaryVertex perimeterVertex
          split_ifs <;> simp_all }
  have hinj : Function.Injective hemb := by
    intro i j hij
    dsimp only [hemb] at hij
    exact perimeterVertex_injective hk hij
  exact cycleGraph_four_mul_not_isAcyclic hk (hT.isAcyclic.comap hemb hinj)

private lemma gridGraph_degree_le_three_of_boundary {n : Nat} (hn : 2 ≤ n)
    (v : GridVertex n n) (hv : IsBoundaryVertex n v) :
    (gridGraph n n).degree v ≤ 3 := by
  have path_degree_le_two (x : Fin n) : (pathGraph n).degree x ≤ 2 := by
    by_cases hx0 : x.val = 0
    · rw [pathGraph_degree_left_end hn x hx0]
      omega
    · by_cases hxN : x.val + 1 = n
      · rw [pathGraph_degree_right_end hn x hxN]
        omega
      · rw [pathGraph_degree_interior x hx0 hxN]
  rw [gridGraph_degree]
  unfold IsBoundaryVertex at hv
  rcases hv with h | h | h | h
  · rw [pathGraph_degree_left_end hn v.1 h]
    have hq := path_degree_le_two v.2
    omega
  · rw [pathGraph_degree_right_end hn v.1 h]
    have hq := path_degree_le_two v.2
    omega
  · rw [pathGraph_degree_left_end hn v.2 h]
    have hp := path_degree_le_two v.1
    omega
  · rw [pathGraph_degree_right_end hn v.2 h]
    have hp := path_degree_le_two v.1
    omega

/-- Each endpoint of an omitted perimeter edge contributes at least one unit
of incidence waste. -/
theorem omitted_perimeter_edge_endpoint_waste {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    {u v : GridVertex n n} (huv : IsPerimeterEdge n u v) (_hnot : ¬T.Adj u v) :
    1 ≤ 3 - (gridGraph n n \ T).degree u ∧
      1 ≤ 3 - (gridGraph n n \ T).degree v := by
  have endpoint (x : GridVertex n n) (hx : IsBoundaryVertex n x) :
      1 ≤ 3 - (gridGraph n n \ T).degree x := by
    rw [degree_sdiff_of_le (gridGraph n n) T hT.le]
    have hgrid := gridGraph_degree_le_three_of_boundary hn x hx
    have htree := tree_degree_pos (by nlinarith) hT x
    omega
  exact ⟨endpoint u huv.2.1, endpoint v huv.2.2⟩

/-- A square grid spanning tree has at least two units of cotree incidence
waste, witnessed by the endpoints of one omitted perimeter edge. -/
theorem two_le_square_cotree_incidenceWaste {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    2 ≤ incidenceWaste (gridGraph n n \ T) := by
  obtain ⟨u, v, huv, hnot⟩ := exists_omitted_perimeter_edge hn hT
  have hw := omitted_perimeter_edge_endpoint_waste hn hT huv hnot
  have hcot : (gridGraph n n \ T).Adj u v := ⟨huv.1, hnot⟩
  have hne : u ≠ v := (gridGraph n n \ T).ne_of_adj hcot
  have hsubset : ({u, v} : Finset (GridVertex n n)) ⊆
      supportFinset (gridGraph n n \ T) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [mem_supportFinset]
      exact Finset.card_pos.mpr ⟨v, by simpa using hcot⟩
    · rw [mem_supportFinset]
      exact Finset.card_pos.mpr ⟨u, by simpa using hcot.symm⟩
  unfold incidenceWaste
  calc
    2 ≤ ∑ x ∈ ({u, v} : Finset (GridVertex n n)),
        (3 - (gridGraph n n \ T).degree x) := by
      simp only [Finset.sum_insert, Finset.mem_singleton, hne, not_false_eq_true,
        Finset.sum_singleton]
      omega
    _ ≤ ∑ x ∈ supportFinset (gridGraph n n \ T),
        (3 - (gridGraph n n \ T).degree x) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by simp)

/-- Cotree waste is congruent to the negative square-grid deficiency modulo
three. -/
theorem square_cotree_incidenceWaste_mod_three {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    (incidenceWaste (gridGraph n n \ T) + D n n) % 3 = 0 := by
  have hw := grid_cotree_incidenceWaste_identity hn hn hT
  omega

/-- In residue one, elementary perimeter waste and the exact cotree congruence
force at least three units of waste. -/
theorem three_le_square_cotree_incidenceWaste_of_mod_three_eq_one {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 = 1)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    3 ≤ incidenceWaste (gridGraph n n \ T) := by
  have htwo := two_le_square_cotree_incidenceWaste hn hT
  have hw := square_cotree_incidenceWaste_mod_three hn hT
  have hnrep : n = 1 + 3 * (n / 3) := by
    have := (Nat.mod_add_div n 3).symm
    omega
  have hDmod : D n n % 3 = 0 := by
    have hsubmod : (n - 1) % 3 = 0 := by omega
    simp [D, Nat.mul_mod, hsubmod]
  rw [Nat.add_mod, hDmod] at hw
  simp only [Nat.add_zero] at hw
  have hWlt := Nat.mod_lt (incidenceWaste (gridGraph n n \ T)) (by omega : 0 < 3)
  omega

/-- In residues zero and two, elementary perimeter waste and the exact cotree
congruence force at least four units of waste. -/
theorem four_le_square_cotree_incidenceWaste_of_mod_three_ne_one {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 ≠ 1)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    4 ≤ incidenceWaste (gridGraph n n \ T) := by
  have htwo := two_le_square_cotree_incidenceWaste hn hT
  have hw := square_cotree_incidenceWaste_mod_three hn hT
  have hnmod := Nat.mod_lt n (by omega : 0 < 3)
  have hnrep := (Nat.mod_add_div n 3).symm
  have hDmod : D n n % 3 = 2 := by
    interval_cases hr : n % 3
    · have hsubmod : (n - 1) % 3 = 2 := by omega
      simp [D, Nat.mul_mod, hsubmod]
    · omega
    · have hsubmod : (n - 1) % 3 = 1 := by omega
      simp [D, Nat.mul_mod, hsubmod]
  rw [Nat.add_mod, hDmod] at hw
  have hWlt := Nat.mod_lt (incidenceWaste (gridGraph n n \ T)) (by omega : 0 < 3)
  interval_cases hr : n % 3
  all_goals omega

/-- Residue-zero specialization of the four-unit waste bound. -/
theorem four_le_square_cotree_incidenceWaste_of_mod_three_eq_zero {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 = 0)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    4 ≤ incidenceWaste (gridGraph n n \ T) :=
  four_le_square_cotree_incidenceWaste_of_mod_three_ne_one hn (by omega) hT

/-- Residue-two specialization of the four-unit waste bound. -/
theorem four_le_square_cotree_incidenceWaste_of_mod_three_eq_two {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 = 2)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    4 ≤ incidenceWaste (gridGraph n n \ T) :=
  four_le_square_cotree_incidenceWaste_of_mod_three_ne_one hn (by omega) hT

/-- Unconditional maximum-preservation upper bound in residue one. -/
theorem maxPreserved_square_le_of_mod_three_eq_one {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 = 1) :
    3 * maxPreserved n n + 3 ≤ n * n + 4 * n - 2 := by
  obtain ⟨T, _, hT, hmax⟩ :=
    exists_spanningSubtree_numPreserved_eq_maxPreserved
      (m := n) (n := n) (by omega) (by omega)
  have hwaste := three_le_square_cotree_incidenceWaste_of_mod_three_eq_one
    hn hmod hT
  have hw := grid_cotree_incidenceWaste_identity hn hn hT
  have hD := D_expand (m := n) (n := n) (by omega) (by omega)
  rw [hmax] at hw
  omega

/-- Unconditional maximum-preservation upper bound in residues zero and two. -/
theorem maxPreserved_square_le_of_mod_three_ne_one {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 ≠ 1) :
    3 * maxPreserved n n + 4 ≤ n * n + 4 * n - 2 := by
  obtain ⟨T, _, hT, hmax⟩ :=
    exists_spanningSubtree_numPreserved_eq_maxPreserved
      (m := n) (n := n) (by omega) (by omega)
  have hwaste := four_le_square_cotree_incidenceWaste_of_mod_three_ne_one
    hn hmod hT
  have hw := grid_cotree_incidenceWaste_identity hn hn hT
  have hD := D_expand (m := n) (n := n) (by omega) (by omega)
  rw [hmax] at hw
  omega

/-- Quotient form of the unconditional residue-one maximum bound. -/
theorem maxPreserved_square_le_quotient_of_mod_three_eq_one {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 = 1) :
    maxPreserved n n ≤ (n * n + 4 * n - 5) / 3 := by
  have h := maxPreserved_square_le_of_mod_three_eq_one hn hmod
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 3)).2
  omega

/-- Quotient form of the unconditional residue-zero/two maximum bound. -/
theorem maxPreserved_square_le_quotient_of_mod_three_ne_one {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 ≠ 1) :
    maxPreserved n n ≤ (n * n + 4 * n - 6) / 3 := by
  have h := maxPreserved_square_le_of_mod_three_ne_one hn hmod
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 3)).2
  omega

/-- Residue-zero specialization of the unconditional maximum bound. -/
theorem maxPreserved_square_le_quotient_of_mod_three_eq_zero {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 = 0) :
    maxPreserved n n ≤ (n * n + 4 * n - 6) / 3 :=
  maxPreserved_square_le_quotient_of_mod_three_ne_one hn (by omega)

/-- Residue-two specialization of the unconditional maximum bound. -/
theorem maxPreserved_square_le_quotient_of_mod_three_eq_two {n : Nat}
    (hn : 2 ≤ n) (hmod : n % 3 = 2) :
    maxPreserved n n ≤ (n * n + 4 * n - 6) / 3 :=
  maxPreserved_square_le_quotient_of_mod_three_ne_one hn (by omega)

end GridGraphs
