import Mathlib

/-!
# Incidence-waste accounting for finite simple graphs

For a graph whose vertex degrees are at most three, `incidenceWaste` sums the
unused capacity `3 - degree` over the non-isolated vertices.  The main results
are stated without natural-number subtraction: the waste and degree ledgers
are additive, and graphs with equally many edges satisfy an exact exchange
balance between newly supported and lost vertices.
-/

namespace GridGraphs

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The non-isolated vertices of a finite simple graph. -/
def supportFinset (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => 0 < G.degree v

/-- Vertices supported by `H` but not by `G`. -/
def newSupport (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    Finset V :=
  supportFinset H \ supportFinset G

/-- Vertices supported by `G` but not by `H`. -/
def lostSupport (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    Finset V :=
  supportFinset G \ supportFinset H

/-- Total unused incidence capacity on the non-isolated vertices. -/
def incidenceWaste (G : SimpleGraph V) [DecidableRel G.Adj] : Nat :=
  ∑ v ∈ supportFinset G, (3 - G.degree v)

omit [DecidableEq V] in
@[simp] theorem mem_supportFinset {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    v ∈ supportFinset G ↔ 0 < G.degree v := by
  simp [supportFinset]

@[simp] theorem mem_newSupport {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {v : V} :
    v ∈ newSupport G H ↔ 0 < H.degree v ∧ G.degree v = 0 := by
  simp [newSupport]

@[simp] theorem mem_lostSupport {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {v : V} :
    v ∈ lostSupport G H ↔ 0 < G.degree v ∧ H.degree v = 0 := by
  simp [lostSupport]

omit [DecidableEq V] in
/-- The support of `G` is mathlib's graph support, represented as a finset. -/
theorem supportFinset_eq_toFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    supportFinset G = G.support.toFinset := by
  ext v
  simp [SimpleGraph.degree_pos_iff_mem_support]

omit [DecidableEq V] in
/-- Closed additive waste ledger before applying the handshaking identity. -/
theorem incidenceWaste_add_degreeSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) :
    incidenceWaste G + ∑ v ∈ supportFinset G, G.degree v =
      3 * (supportFinset G).card := by
  rw [incidenceWaste, ← Finset.sum_add_distrib]
  calc
    ∑ v ∈ supportFinset G, (3 - G.degree v + G.degree v) =
        ∑ _v ∈ supportFinset G, 3 := by
          apply Finset.sum_congr rfl
          intro v _
          have := hdeg v
          omega
    _ = 3 * (supportFinset G).card := by simp [Nat.mul_comm]

omit [DecidableEq V] in
/-- Closed additive incidence-waste identity for a graph of maximum degree
three.  It avoids truncated subtraction in the theorem statement. -/
theorem incidenceWaste_add_twice_card_edges (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ 3) :
    incidenceWaste G + 2 * G.edgeFinset.card = 3 * (supportFinset G).card := by
  rw [← G.sum_degrees_support_eq_twice_card_edges,
    ← supportFinset_eq_toFinset G]
  exact incidenceWaste_add_degreeSum G hdeg

/-- Support-cardinality balance, with no cardinal subtraction. -/
theorem support_card_add_newSupport (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (supportFinset G).card + (newSupport G H).card =
      (supportFinset H).card + (lostSupport G H).card := by
  unfold newSupport lostSupport
  have hG := Finset.card_sdiff_add_card_inter (supportFinset G) (supportFinset H)
  have hH := Finset.card_sdiff_add_card_inter (supportFinset H) (supportFinset G)
  rw [Finset.inter_comm (supportFinset H) (supportFinset G)] at hH
  omega

/-- Arbitrary equal-edge exchange balance.  No containment or one-edge
exchange hypothesis is needed: only the edge counts and degree bounds matter. -/
theorem incidenceWaste_exchange_balance (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : ∀ v, G.degree v ≤ 3) (hH : ∀ v, H.degree v ≤ 3)
    (hedges : G.edgeFinset.card = H.edgeFinset.card) :
    incidenceWaste G + 3 * (newSupport G H).card =
      incidenceWaste H + 3 * (lostSupport G H).card := by
  have hGw := incidenceWaste_add_twice_card_edges G hG
  have hHw := incidenceWaste_add_twice_card_edges H hH
  have hs := support_card_add_newSupport G H
  omega

/-- Signed form of the exchange balance.  The natural-number identity above is
the primary statement; this version is convenient for delta calculations. -/
theorem incidenceWaste_int_delta (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : ∀ v, G.degree v ≤ 3) (hH : ∀ v, H.degree v ≤ 3)
    (hedges : G.edgeFinset.card = H.edgeFinset.card) :
    (incidenceWaste H : Int) - incidenceWaste G =
      3 * ((newSupport G H).card - (lostSupport G H).card) := by
  have h := incidenceWaste_exchange_balance G H hG hH hedges
  omega

/-- A waste-minimizing graph cannot lose more support vertices than an
equal-edge competitor newly introduces. -/
theorem lostSupport_card_le_newSupport_of_waste_le (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : ∀ v, G.degree v ≤ 3) (hH : ∀ v, H.degree v ≤ 3)
    (hedges : G.edgeFinset.card = H.edgeFinset.card)
    (hwaste : incidenceWaste G ≤ incidenceWaste H) :
    (lostSupport G H).card ≤ (newSupport G H).card := by
  have h := incidenceWaste_exchange_balance G H hG hH hedges
  omega

/-- Strict waste improvement is exactly strict support improvement for graphs
with equal edge counts. -/
theorem incidenceWaste_lt_iff_newSupport_lt_lostSupport (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : ∀ v, G.degree v ≤ 3) (hH : ∀ v, H.degree v ≤ 3)
    (hedges : G.edgeFinset.card = H.edgeFinset.card) :
    incidenceWaste H < incidenceWaste G ↔
      (newSupport G H).card < (lostSupport G H).card := by
  have h := incidenceWaste_exchange_balance G H hG hH hedges
  omega

/-- Equal waste is exactly equal support turnover for graphs with equal edge
counts. -/
theorem incidenceWaste_eq_iff_newSupport_card_eq_lostSupport_card
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : ∀ v, G.degree v ≤ 3) (hH : ∀ v, H.degree v ≤ 3)
    (hedges : G.edgeFinset.card = H.edgeFinset.card) :
    incidenceWaste H = incidenceWaste G ↔
      (newSupport G H).card = (lostSupport G H).card := by
  have h := incidenceWaste_exchange_balance G H hG hH hedges
  omega

end GridGraphs
