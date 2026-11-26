import GridGraphs.Accounting.ForcedForestLedger
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace GridGraphs.CapBill
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Directed incidences arriving at `v` from `S`. -/
def hits (S : Finset V) (v : V) : Int := (S.filter fun w => G.Adj w v).card

omit [Fintype V] [DecidableEq V] in
theorem count_both_ways (S T : Finset V) :
    ∑ v ∈ T, hits G S v = ∑ v ∈ S, hits G T v := by
  unfold hits
  norm_cast
  simpa only [bipartiteBelow,bipartiteAbove,adj_comm] using
    (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj (s:=S) (t:=T)).symm

def iso (F : Finset V) (v : V) : Int := if v ∉ F ∧ hits G F v=0 then 1 else 0

/-- `N` is the set of noncentral sites, not the set of marks. The two
endpoints of a central singleton are counted separately. -/
def siteBill (F N : Finset V) (v : V) : Int :=
  (if v ∈ F ∧ v ∉ N then 2-hits G F v else 0) +
  (if v ∈ N then iso G F v else 2*iso G F v) +
  (if v ∉ F ∧ v ∈ N ∧ hits G F v=2 then 1 else 0)

omit [Fintype V] in
private theorem pointwise (F N : Finset V) (v : V)
    (cap : v ∉ F → v ∈ N → hits G F v ≤ 2) :
    siteBill G F N v - 2*iso G F v =
      (if v ∈ F then (if v ∈ N then 1 else 2) - hits G F v else 0) +
      (if v ∈ N then hits G F v-1 else 0) := by
  have pos : 0 ≤ hits G F v := Int.natCast_nonneg _
  by_cases hf : v ∈ F <;> by_cases hn : v ∈ N <;>
    simp_all [siteBill,iso]
  split_ifs <;> omega

theorem geometric_sum (F N : Finset V)
    (blank : ∀ v ∉ F, v ∈ N → hits G F v ≤ 2)
    (neighbors : ∀ v ∈ F, hits G N v = if v ∈ N then 3 else 2) :
    (∑ v, siteBill G F N v) - 2*(∑ v, iso G F v) =
      4*F.card - (∑ v ∈ F, hits G F v) - N.card := by
  rw [Finset.mul_sum,← sum_sub_distrib]
  simp_rw [pointwise G F N _ (blank _)]
  rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  simp only [filter_mem_eq_inter,univ_inter,sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one]
  rw [count_both_ways G F N]
  have h : (∑ v ∈ F, (if v ∈ N then (1:ℤ) else 2)) + (∑ v ∈ F, hits G N v) =
      4*F.card := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _v ∈ F, (4:ℤ) := by
        apply sum_congr rfl
        intro v hv; rw [neighbors _ hv]; split_ifs <;> decide
      _ = _ := by simp [mul_comm]
  omega

omit [DecidableEq V] in
theorem hits_univ (v : V) : hits G univ v = G.degree v := by
  have eq : univ.filter (fun w => G.Adj w v) = G.neighborFinset v := by
    ext w; simp [adj_comm]
  unfold hits; rw [eq]; rfl

theorem forced_degrees (F : Finset V) :
    2*((forcedEdgeGraph G (↑F : Set V)).edgeFinset.card : Int) =
      2*(∑ v ∈ F, (G.degree v : Int)) - ∑ v ∈ F, hits G F v := by
  let H := forcedEdgeGraph G (↑F : Set V)
  have deg (v : V) : (H.degree v : Int) =
      hits G F v + (if v ∈ F then (G.degree v : Int)-hits G F v else 0) := by
    by_cases hv : v ∈ F
    · have e : H.neighborFinset v = G.neighborFinset v := by
        ext w; simp only [mem_neighborFinset]
        exact and_iff_left (Or.inl hv)
      have d : H.degree v = G.degree v := congrArg Finset.card e
      simp [hv,d]
    · have e : H.neighborFinset v = F.filter (fun w => G.Adj w v) := by
        ext w; simp only [mem_neighborFinset,mem_filter]
        change G.Adj v w ∧ (v ∈ F ∨ w ∈ F) ↔ _
        simp [hv,and_comm,adj_comm]
      simp only [if_neg hv,add_zero,hits,SimpleGraph.degree,e]
  have h := H.sum_degrees_eq_twice_card_edges
  have eq : (∑ v, (H.degree v : Int)) = 2*(H.edgeFinset.card : Int) := by exact_mod_cast h
  rw [←eq]
  simp_rw [deg]
  rw [sum_add_distrib, ← sum_filter]
  simp only [filter_mem_eq_inter,univ_inter,sum_sub_distrib]
  rw [count_both_ways G F univ]
  simp_rw [hits_univ]
  ring

/-- Counting theorem on a padded rectangular forest. `extras` subtracts
blank isolates and the terminal classes from the *actual* component count. -/
theorem colored_bill (F N : Finset V) (r h j : Nat)
    (forest : (forcedEdgeGraph G (↑F : Set V)).IsAcyclic)
    (volume : Fintype.card V=3*r*(h+2)) (noncentral : N.card=2*r*(h+2))
    (blank : ∀ v ∉ F, v ∈ N → hits G F v ≤ 2)
    (neighbors : ∀ v ∈ F, hits G N v = if v ∈ N then 3 else 2)
    (boundary : (∑ v ∈ F, (G.degree v : Int))=4*F.card-r) :
    let bonus := (F.card : Int)-r*((h:ℤ)+1)
    let extras := (Fintype.card (forcedEdgeGraph G (↑F : Set V)).ConnectedComponent : Int) -
      (∑ v, iso G F v) - ((r:ℤ)-j)
    let bill := (∑ v, siteBill G F N v)-2*r+2*extras
    4*bonus=2*r+2*j-bill := by
  dsimp only
  have geom := geometric_sum G F N blank neighbors
  have deg := forced_degrees G F
  rw [boundary] at deg
  have fc := forcedEdgeGraph_forest_ledger G F forest
  rw [volume] at fc
  zify at fc noncentral
  linarith only [geom,deg,fc,noncentral]

end GridGraphs.CapBill
