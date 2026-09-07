import Mathlib

/-!
# Physical-union edge capacity and interior three-rod closure

Intervals supplied to `edge_capacity` must cover all surviving eligible columns,
including both side-boundary pieces. They need not be disjoint: overlapping
covers give valid, possibly weaker, upper bounds. No W2 geometry is assumed.

The main result is `three_horizontal_rods_certificate`: three interior rods
with the stated column bounds and pairwise overlap geometry satisfy the exact
joint-capacity certificate. `interior_three_rod_deficit` also handles fewer
rods by allowing empty horizontal edge-column sets.
-/

namespace GridGraphs.CarrierLayers.MixedPacking

open Finset

/-- The spacing condition on eligible vertical FF columns. -/
def Spaced (V : Finset Nat) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, x < y → x + 3 ≤ y

/-- Three-spaced points in a closed interval fit in its three-column blocks.
The formula also handles an empty interval. -/
theorem interval_capacity (V : Finset Nat) (a b : Nat)
    (hV : V ⊆ Icc a b) (hspace : Spaced V) :
    V.card ≤ (b + 1 - a + 2) / 3 := by
  have hinj : Set.InjOn (fun x : Nat => (x - a) / 3) V := by
    intro x hx y hy heq
    dsimp only at heq
    have hxI := mem_Icc.mp (hV hx)
    have hyI := mem_Icc.mp (hV hy)
    rcases lt_trichotomy x y with h | h | h
    · have := hspace x hx y hy h
      omega
    · exact h
    · have := hspace y hy x hx h
      omega
  have hsub : V.image (fun x => (x - a) / 3) ⊆
      range ((b + 1 - a + 2) / 3) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    have := mem_Icc.mp (hV hx)
    simp only [mem_range]
    omega
  calc
    V.card = (V.image (fun x => (x - a) / 3)).card := (card_image_of_injOn hinj).symm
    _ ≤ (range ((b + 1 - a + 2) / 3)).card := card_le_card hsub
    _ = _ := card_range _

/-- Local physical-union capacity. `hcover` includes every surviving column;
in particular it cannot omit either side-boundary surviving interval. -/
theorem edge_capacity (V : Finset Nat) (bands : Finset (Nat × Nat))
    (hspace : Spaced V)
    (hcover : ∀ x ∈ V, ∃ p ∈ bands, x ∈ Icc p.1 p.2) :
    V.card ≤ ∑ p ∈ bands, (p.2 + 1 - p.1 + 2) / 3 := by
  have hsub : V ⊆ bands.biUnion (fun p => V ∩ Icc p.1 p.2) := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hcover x hx
    exact mem_biUnion.mpr ⟨p, hp, mem_inter.mpr ⟨hx, hxp⟩⟩
  calc
    V.card ≤ (bands.biUnion (fun p => V ∩ Icc p.1 p.2)).card := card_le_card hsub
    _ ≤ ∑ p ∈ bands, (V ∩ Icc p.1 p.2).card := card_biUnion_le
    _ ≤ _ := sum_le_sum fun p _ => interval_capacity _ _ _ inter_subset_right
      (fun x hx y hy hxy => hspace x (mem_inter.mp hx).1 y (mem_inter.mp hy).1 hxy)

/-- Sum local capacities without adding losses from overlapping rod shadows.
Apply to the surviving intervals of the physical shadow union at each step. -/
theorem global_deficit {ι : Type*} [DecidableEq ι]
    (steps : Finset ι) (V : ι → Finset Nat) (bands : ι → Finset (Nat × Nat))
    (Q : Nat) (hspace : ∀ t ∈ steps, Spaced (V t))
    (hcover : ∀ t ∈ steps, ∀ x ∈ V t, ∃ p ∈ bands t, x ∈ Icc p.1 p.2) :
    steps.sum (fun t => Q - (bands t).sum (fun p => (p.2 + 1 - p.1 + 2) / 3)) ≤
      steps.sum (fun t => Q - (V t).card) := by
  apply sum_le_sum
  intro t ht
  exact Nat.sub_le_sub_left (edge_capacity (V t) (bands t) (hspace t ht) (hcover t ht)) Q

/-! ## Checked top-row obstructions at k = 5

Here N = 13, A = [3,13], Q = 4. A single rod occupies [5,b] in
row 1. The definitions retain all twelve steps, both boundary intervals,
and the clipped physical shadow. These are capacity-model counterexamples,
not feasible forced forests or consequences of the paper-only W2 premises.
-/

def topShadow (b t : Nat) : Finset Nat :=
  if t ≤ 2 then Icc 3 13 ∩ Icc 4 (b + 1) else ∅

def topBands (b t : Nat) : Finset (Nat × Nat) :=
  if t ≤ 2 then {(3, 3), (b + 2, 13)} else {(3, 13)}

def topWitness (b t : Nat) : Finset Nat :=
  if t ≤ 2 then (if b = 8 then {3, 10, 13} else {3, 13})
  else {3, 6, 9, 12}

/-- Exact physical complement, including the left singleton and right tail.
The witnesses attain the sum of interval capacities at every valid step. -/
theorem top_examples_local :
    ∀ b ∈ ({8, 11} : Finset Nat), ∀ t ∈ Icc 1 12,
      (topBands b t).biUnion (fun p => Icc p.1 p.2) = Icc 3 13 \ topShadow b t ∧
      topWitness b t ⊆ Icc 3 13 \ topShadow b t ∧
      Spaced (topWitness b t) ∧
      (topWitness b t).card =
        (topBands b t).sum (fun p => (p.2 + 1 - p.1 + 2) / 3) := by
  unfold Spaced
  decide

/-- The displayed union capacities are maxima, not merely upper estimates. -/
theorem top_examples_maximum (b t : Nat) (hb : b ∈ ({8, 11} : Finset Nat))
    (ht : t ∈ Icc 1 12) (V : Finset Nat)
    (hV : V ⊆ Icc 3 13 \ topShadow b t) (hspace : Spaced V) :
    V.card ≤ (topWitness b t).card := by
  obtain ⟨hbands, _, _, hcard⟩ := top_examples_local b hb t ht
  rw [hcard]
  apply edge_capacity V (topBands b t) hspace
  intro x hx
  have hmem := hV hx
  rw [← hbands] at hmem
  exact mem_biUnion.mp hmem

/-- Length four costs three horizontal edges, but its exact certificate is two. -/
theorem top_length_four_certificate_fails :
    (Icc 1 12).sum (fun t => 4 - (topWitness 8 t).card) = 2 ∧
    2 < 8 - 5 := by
  decide

/-- Length seven costs six horizontal edges, but its exact certificate is four. -/
theorem top_length_seven_certificate_fails :
    (Icc 1 12).sum (fun t => 4 - (topWitness 11 t).card) = 4 ∧
    4 < 11 - 5 := by
  decide

/-- At k = 5, the interior rod [5,8] in row 2 affects exactly steps 1,2,3.
Its physical-union certificate is exactly H = 3, not strictly larger.
Thus strictness at k = 5 requires additional forced-graph geometry. -/
theorem interior_k_five_equality :
    (∀ t ∈ Icc 1 12,
      (topBands 8 (t - 1)).biUnion (fun p => Icc p.1 p.2) =
        Icc 3 13 \ topShadow 8 (t - 1) ∧
      topWitness 8 (t - 1) ⊆ Icc 3 13 \ topShadow 8 (t - 1) ∧
      Spaced (topWitness 8 (t - 1)) ∧
      (topWitness 8 (t - 1)).card =
        (topBands 8 (t - 1)).sum (fun p => (p.2 + 1 - p.1 + 2) / 3)) ∧
    (Icc 1 12).sum (fun t => 4 - (topWitness 8 (t - 1)).card) = 8 - 5 := by
  unfold Spaced
  decide

/-! ## Joint horizontal-edge packing

Use the left column of each horizontal edge, rather than charging rods
independently. Distinct edge columns contribute distinct endpoint resources.
-/

/-- Exact local hypotheses: all columns lie in the eligible interval, vertical
columns are three-spaced, and every horizontal edge excludes its four-column
shadow. The endpoints of a horizontal edge at x are x and x+1. -/
def EdgeCompatible (Q : Nat) (V E : Finset Nat) : Prop :=
  Spaced V ∧ V ⊆ Icc 3 (3 * Q + 1) ∧ E ⊆ Icc 2 (3 * Q + 1) ∧
    ∀ v ∈ V, ∀ x ∈ E, v + 1 < x ∨ x + 2 < v

/-- Joint shadow inequality, with both side boundaries included. This counts
physical horizontal edge columns only once, regardless of their rod labels. -/
theorem joint_edge_capacity (Q : Nat) (V E : Finset Nat)
    (h : EdgeCompatible Q V E) : 3 * V.card + E.card ≤ 3 * Q := by
  obtain ⟨hspace, hV, hE, havoid⟩ := h
  by_cases hempty : E = ∅
  · have hv := interval_capacity V 3 (3 * Q + 1) hV hspace
    simp only [hempty, card_empty, Nat.add_zero]
    omega
  have hnonempty : E.Nonempty := nonempty_iff_ne_empty.mpr hempty
  let U := E ∪ E.image (fun x => x + 1)
  let B := (V ×ˢ range 3).image (fun p => p.1 + p.2 - 1)
  have hinj : Set.InjOn (fun p : Nat × Nat => p.1 + p.2 - 1)
      (↑(V ×ˢ range 3) : Set (Nat × Nat)) := by
    intro p hp q hq heq
    obtain ⟨hpV, hpR⟩ := mem_product.mp hp
    obtain ⟨hqV, hqR⟩ := mem_product.mp hq
    have hpI := mem_Icc.mp (hV hpV)
    have hqI := mem_Icc.mp (hV hqV)
    have hp3 := mem_range.mp hpR
    have hq3 := mem_range.mp hqR
    dsimp only at heq
    have heqv : p.1 = q.1 := by
      rcases lt_trichotomy p.1 q.1 with hlt | he | hlt
      · have := hspace p.1 hpV q.1 hqV hlt
        omega
      · exact he
      · have := hspace q.1 hqV p.1 hpV hlt
        omega
    apply Prod.ext heqv
    omega
  have hBcard : B.card = 3 * V.card := by
    dsimp [B]
    rw [card_image_of_injOn hinj, card_product, card_range]
    omega
  have hUcard : E.card + 1 ≤ U.card := by
    let x := E.max' hnonempty
    have hx : x ∈ E := max'_mem E hnonempty
    have hnot : x + 1 ∉ E := by
      intro hmem
      have := le_max' E (x + 1) hmem
      omega
    have hsub : insert (x + 1) E ⊆ U := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact mem_union_right _ (mem_image.mpr ⟨x, hx, rfl⟩)
      · exact mem_union_left _ hz
    have := card_le_card hsub
    rw [card_insert_of_notMem hnot] at this
    exact this
  have hBU : Disjoint B U := by
    apply disjoint_left.mpr
    intro z hzB hzU
    obtain ⟨⟨v, i⟩, hvi, rfl⟩ := mem_image.mp hzB
    obtain ⟨hv, hi⟩ := mem_product.mp hvi
    have hvI := mem_Icc.mp (hV hv)
    have hi3 := mem_range.mp hi
    rcases mem_union.mp hzU with hz | hz
    · have := havoid v hv (v + i - 1) hz
      omega
    · obtain ⟨x, hx, he⟩ := mem_image.mp hz
      have := havoid v hv x hx
      omega
  have hsub : B ∪ U ⊆ Icc 2 (3 * Q + 2) := by
    intro z hz
    apply mem_Icc.mpr
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨⟨v, i⟩, hvi, rfl⟩ := mem_image.mp hz
      obtain ⟨hv, hi⟩ := mem_product.mp hvi
      have := mem_Icc.mp (hV hv)
      have := mem_range.mp hi
      constructor <;> omega
    · rcases mem_union.mp hz with hz | hz
      · have := mem_Icc.mp (hE hz)
        constructor <;> omega
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
        have := mem_Icc.mp (hE hx)
        constructor <;> omega
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hBU, hBcard, Nat.card_Icc] at hcount
  omega

/-- The original-interval overlap bound of one prevents reuse of horizontal
edge columns. This applies to each pair of rods in a three-row window. -/
theorem rod_edge_columns_disjoint (a b c d : Nat)
    (h : (Icc a b ∩ Icc c d).card ≤ 1) : Disjoint (Ico a b) (Ico c d) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hxI := mem_Ico.mp hx
  have hyI := mem_Ico.mp hy
  have h0 : x ∈ Icc a b ∩ Icc c d := by
    simp only [mem_inter, mem_Icc]
    omega
  have h1 : x + 1 ∈ Icc a b ∩ Icc c d := by
    simp only [mem_inter, mem_Icc]
    omega
  have := card_le_one.mp h x h0 (x + 1) h1
  omega

/-- All horizontal edges on rows y,y+1,y+2 are paid by the four valid
steps y-1,y,y+1,y+2. E0,E1,E2 are their edge-column sets. Pairwise disjointness
is supplied by the rod geometry, not by independent shadow-loss charges.
The result allows arbitrarily many rods within this three-row window. -/
theorem three_row_window_deficit (Q : Nat) (E0 E1 E2 V0 V1 V2 V3 : Finset Nat)
    (h01 : Disjoint E0 E1) (h02 : Disjoint E0 E2) (h12 : Disjoint E1 E2)
    (h0 : EdgeCompatible Q V0 (E0 ∪ E1))
    (h1 : EdgeCompatible Q V1 (E0 ∪ E1 ∪ E2))
    (h2 : EdgeCompatible Q V2 (E0 ∪ E1 ∪ E2))
    (h3 : EdgeCompatible Q V3 (E1 ∪ E2)) :
    E0.card + E1.card + E2.card ≤
      (Q - V0.card) + (Q - V1.card) + (Q - V2.card) + (Q - V3.card) := by
  have h012 : Disjoint (E0 ∪ E1) E2 := disjoint_union_left.mpr ⟨h02, h12⟩
  have hc0 := joint_edge_capacity Q V0 (E0 ∪ E1) h0
  have hc1 := joint_edge_capacity Q V1 (E0 ∪ E1 ∪ E2) h1
  have hc2 := joint_edge_capacity Q V2 (E0 ∪ E1 ∪ E2) h2
  have hc3 := joint_edge_capacity Q V3 (E1 ∪ E2) h3
  rw [card_union_of_disjoint h01] at hc0
  rw [card_union_of_disjoint h012, card_union_of_disjoint h01] at hc1 hc2
  rw [card_union_of_disjoint h12] at hc3
  omega

/-- Three interior rows admit three selected affected steps each. Selected
bands for rows at distance at least three are disjoint. Nearby rows may share
steps, where `joint_edge_capacity` handles their physical union instead.
The only forward shifts propagate from row 2 along a chain of gaps of three;
with three rods that chain ends by row 8, safely below N >= 13. -/
theorem three_rod_schedule (N r0 r1 r2 : Nat) (hN : 13 ≤ N)
    (hlo : 2 ≤ r0) (h01 : r0 ≤ r1) (h12 : r1 ≤ r2) (hhi : r2 < N) :
    ∃ T0 T1 T2 : Finset Nat,
      (T0 ⊆ Icc 1 (N - 1) ∧ T0 ⊆ Icc (r0 - 2) (r0 + 1) ∧ T0.card = 3) ∧
      (T1 ⊆ Icc 1 (N - 1) ∧ T1 ⊆ Icc (r1 - 2) (r1 + 1) ∧ T1.card = 3) ∧
      (T2 ⊆ Icc 1 (N - 1) ∧ T2 ⊆ Icc (r2 - 2) (r2 + 1) ∧ T2.card = 3) ∧
      (r0 + 3 ≤ r1 → Disjoint T0 T1) ∧
      (r0 + 3 ≤ r2 → Disjoint T0 T2) ∧
      (r1 + 3 ≤ r2 → Disjoint T1 T2) := by
  let s0 := max 1 (r0 - 2)
  let s1 := max (max 1 (r1 - 2)) (if r0 + 3 ≤ r1 then s0 + 3 else 0)
  let s2 := max (max (max 1 (r2 - 2)) (if r0 + 3 ≤ r2 then s0 + 3 else 0))
    (if r1 + 3 ≤ r2 then s1 + 3 else 0)
  have hs :
      (1 ≤ s0 ∧ r0 - 2 ≤ s0 ∧ s0 + 2 ≤ r0 + 1 ∧ s0 + 2 < N) ∧
      (1 ≤ s1 ∧ r1 - 2 ≤ s1 ∧ s1 + 2 ≤ r1 + 1 ∧ s1 + 2 < N) ∧
      (1 ≤ s2 ∧ r2 - 2 ≤ s2 ∧ s2 + 2 ≤ r2 + 1 ∧ s2 + 2 < N) ∧
      (r0 + 3 ≤ r1 → s0 + 3 ≤ s1) ∧
      (r0 + 3 ≤ r2 → s0 + 3 ≤ s2) ∧
      (r1 + 3 ≤ r2 → s1 + 3 ≤ s2) := by
    dsimp [s0, s1, s2]
    split_ifs <;> omega
  have hband (r s : Nat) (hs : 1 ≤ s ∧ r - 2 ≤ s ∧ s + 2 ≤ r + 1 ∧ s + 2 < N) :
      Icc s (s + 2) ⊆ Icc 1 (N - 1) ∧
      Icc s (s + 2) ⊆ Icc (r - 2) (r + 1) ∧ (Icc s (s + 2)).card = 3 := by
    constructor
    · intro t ht
      simp only [mem_Icc] at ht ⊢
      omega
    constructor
    · intro t ht
      simp only [mem_Icc] at ht ⊢
      omega
    · rw [Nat.card_Icc]
      omega
  have hdisj (s t : Nat) (hst : s + 3 ≤ t) : Disjoint (Icc s (s + 2)) (Icc t (t + 2)) := by
    apply disjoint_left.mpr
    intro x hx hy
    simp only [mem_Icc] at hx hy
    omega
  exact ⟨Icc s0 (s0 + 2), Icc s1 (s1 + 2), Icc s2 (s2 + 2),
    hband r0 s0 hs.1, hband r1 s1 hs.2.1, hband r2 s2 hs.2.2.1,
    fun h => hdisj s0 s1 (hs.2.2.2.1 h),
    fun h => hdisj s0 s2 (hs.2.2.2.2.1 h),
    fun h => hdisj s1 s2 (hs.2.2.2.2.2 h)⟩

theorem EdgeCompatible.union {Q : Nat} {V E F : Finset Nat}
    (hE : EdgeCompatible Q V E) (hF : EdgeCompatible Q V F) :
    EdgeCompatible Q V (E ∪ F) := by
  obtain ⟨hs, hv, he, hae⟩ := hE
  obtain ⟨_, _, hf, haf⟩ := hF
  refine ⟨hs, hv, union_subset he hf, ?_⟩
  intro v hvm x hx
  rcases mem_union.mp hx with hx | hx
  · exact hae v hvm x hx
  · exact haf v hvm x hx

/-- Three selected occurrences of every horizontal edge suffice, provided
simultaneously selected edge sets are disjoint. This is a physical-union
count: no independent rod deficit inequality is used. -/
theorem scheduled_edge_charge (Q : Nat) (steps T0 T1 T2 E0 E1 E2 : Finset Nat)
    (V : Nat → Finset Nat)
    (hT0 : T0 ⊆ steps) (hT1 : T1 ⊆ steps) (hT2 : T2 ⊆ steps)
    (hc0 : T0.card = 3) (hc1 : T1.card = 3) (hc2 : T2.card = 3)
    (hC0 : ∀ t ∈ steps, EdgeCompatible Q (V t) (if t ∈ T0 then E0 else ∅))
    (hC1 : ∀ t ∈ steps, EdgeCompatible Q (V t) (if t ∈ T1 then E1 else ∅))
    (hC2 : ∀ t ∈ steps, EdgeCompatible Q (V t) (if t ∈ T2 then E2 else ∅))
    (hD01 : ∀ t ∈ T0, t ∈ T1 → Disjoint E0 E1)
    (hD02 : ∀ t ∈ T0, t ∈ T2 → Disjoint E0 E2)
    (hD12 : ∀ t ∈ T1, t ∈ T2 → Disjoint E1 E2) :
    E0.card + E1.card + E2.card ≤ steps.sum (fun t => Q - (V t).card) := by
  have hdisj (t : Nat) (S T E F : Finset Nat)
      (h : t ∈ S → t ∈ T → Disjoint E F) :
      Disjoint (if t ∈ S then E else ∅) (if t ∈ T then F else ∅) := by
    split_ifs with hs ht ht
    · exact h hs ht
    · exact disjoint_empty_right _
    · exact disjoint_empty_left _
    · exact disjoint_empty_left _
  have hlocal : ∀ t ∈ steps,
      (if t ∈ T0 then E0.card else 0) + (if t ∈ T1 then E1.card else 0) +
        (if t ∈ T2 then E2.card else 0) ≤ 3 * (Q - (V t).card) := by
    intro t ht
    have hd01 := hdisj t T0 T1 E0 E1 (hD01 t)
    have hd02 := hdisj t T0 T2 E0 E2 (hD02 t)
    have hd12 := hdisj t T1 T2 E1 E2 (hD12 t)
    have hcap := joint_edge_capacity Q (V t) _ (((hC0 t ht).union (hC1 t ht)).union (hC2 t ht))
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hd02, hd12⟩),
      card_union_of_disjoint hd01] at hcap
    simp only [apply_ite Finset.card, card_empty] at hcap
    omega
  have hcount (T E : Finset Nat) (hT : T ⊆ steps) (hc : T.card = 3) :
      steps.sum (fun t => if t ∈ T then E.card else 0) = 3 * E.card := by
    have hf : steps.filter (fun t => t ∈ T) = T := by
      ext t
      simp only [mem_filter]
      exact ⟨And.right, fun ht => ⟨hT ht, ht⟩⟩
    rw [← sum_filter, hf, sum_const, hc, nsmul_eq_mul]
    norm_num
  have hsum := sum_le_sum hlocal
  rw [sum_add_distrib, sum_add_distrib, hcount T0 E0 hT0 hc0,
    hcount T1 E1 hT1 hc1, hcount T2 E2 hT2 hc2, ← mul_sum] at hsum
  omega

/-- Interior mixed packing for three rods, at arbitrary sorted rows. E_i is
the set of left columns of horizontal edges of rod i (normally Ico a_i b_i).
The geometric premises require disjoint edge columns only for row distances
at most two. Same/adjacent-row separation and the distance-two overlap bound
of one imply exactly this, via `rod_edge_columns_disjoint`.

All eligible columns, all valid steps, and the complete four-step shadows
are explicit. This proves H <= Delta, not an assumption of that inequality.
Empty E_i allow fewer than three rods. No top-row rod is admitted. -/
theorem interior_three_rod_deficit (Q r0 r1 r2 : Nat) (hQ : 4 ≤ Q)
    (hlo : 2 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hhi : r2 < 3 * Q + 1)
    (E0 E1 E2 : Finset Nat) (V : Nat → Finset Nat)
    (hE0 : E0 ⊆ Icc 2 (3 * Q + 1)) (hE1 : E1 ⊆ Icc 2 (3 * Q + 1))
    (hE2 : E2 ⊆ Icc 2 (3 * Q + 1))
    (hgeom01 : r1 ≤ r0 + 2 → Disjoint E0 E1)
    (hgeom02 : r2 ≤ r0 + 2 → Disjoint E0 E2)
    (hgeom12 : r2 ≤ r1 + 2 → Disjoint E1 E2)
    (hV : ∀ t ∈ Icc 1 (3 * Q), Spaced (V t) ∧ V t ⊆ Icc 3 (3 * Q + 1))
    (hshadow0 : ∀ t ∈ Icc 1 (3 * Q), t ∈ Icc (r0 - 2) (r0 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E0, v + 1 < x ∨ x + 2 < v)
    (hshadow1 : ∀ t ∈ Icc 1 (3 * Q), t ∈ Icc (r1 - 2) (r1 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E1, v + 1 < x ∨ x + 2 < v)
    (hshadow2 : ∀ t ∈ Icc 1 (3 * Q), t ∈ Icc (r2 - 2) (r2 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E2, v + 1 < x ∨ x + 2 < v) :
    E0.card + E1.card + E2.card ≤ (Icc 1 (3 * Q)).sum (fun t => Q - (V t).card) := by
  obtain ⟨T0, T1, T2, hT0, hT1, hT2, hd01, hd02, hd12⟩ :=
    three_rod_schedule (3 * Q + 1) r0 r1 r2 (by omega) hlo hr01 hr12 hhi
  have hsteps : 3 * Q + 1 - 1 = 3 * Q := by omega
  rw [hsteps] at hT0 hT1 hT2
  have hcompat (r : Nat) (E T : Finset Nat)
      (hE : E ⊆ Icc 2 (3 * Q + 1)) (hT : T ⊆ Icc (r - 2) (r + 1))
      (hshadow : ∀ t ∈ Icc 1 (3 * Q), t ∈ Icc (r - 2) (r + 1) →
        ∀ v ∈ V t, ∀ x ∈ E, v + 1 < x ∨ x + 2 < v) :
      ∀ t ∈ Icc 1 (3 * Q), EdgeCompatible Q (V t) (if t ∈ T then E else ∅) := by
    intro t ht
    obtain ⟨hs, hv⟩ := hV t ht
    split_ifs with hm
    · exact ⟨hs, hv, hE, hshadow t ht (hT hm)⟩
    · exact ⟨hs, hv, empty_subset _, by simp⟩
  have hdisjoint (r s : Nat) (E F T U : Finset Nat)
      (hg : s ≤ r + 2 → Disjoint E F) (hd : r + 3 ≤ s → Disjoint T U) :
      ∀ t ∈ T, t ∈ U → Disjoint E F := by
    intro t ht hu
    by_cases hnear : s ≤ r + 2
    · exact hg hnear
    · exact (disjoint_left.mp (hd (by omega)) ht hu).elim
  exact scheduled_edge_charge Q (Icc 1 (3 * Q)) T0 T1 T2 E0 E1 E2 V
    hT0.1 hT1.1 hT2.1 hT0.2.2 hT1.2.2 hT2.2.2
    (hcompat r0 E0 T0 hE0 hT0.2.1 hshadow0)
    (hcompat r1 E1 T1 hE1 hT1.2.1 hshadow1)
    (hcompat r2 E2 T2 hE2 hT2.2.1 hshadow2)
    (hdisjoint r0 r1 E0 E1 T0 T1 hgeom01 hd01)
    (hdisjoint r0 r2 E0 E2 T0 T2 hgeom02 hd02)
    (hdisjoint r1 r2 E1 E2 T1 T2 hgeom12 hd12)

/-- Boundary hypotheses for a horizontal rod. The eligible vertical columns
are [3,N], N=3Q+1; rod vertices may use the larger interval [2,N+1]. These
column bounds are explicit premises, not inferred from paper-only W2. -/
structure InteriorRod (Q : Nat) where
  row : Nat
  left : Nat
  right : Nat
  row_bounds : 2 ≤ row ∧ row < 3 * Q + 1
  column_bounds : 2 ≤ left ∧ right ≤ 3 * Q + 2
  nontrivial : left + 1 ≤ right

/-- The full four-step, expanded-column exclusion, clipped implicitly by
the eligible-column hypothesis on V. -/
def InteriorRod.Excludes {Q : Nat} (R : InteriorRod Q) (V : Nat → Finset Nat) : Prop :=
  ∀ t ∈ Icc 1 (3 * Q), t ∈ Icc (R.row - 2) (R.row + 1) →
    Disjoint (V t) (Icc (R.left - 1) (R.right + 1))

/-- Concrete interval-rod form of the full interior theorem. The overlap
premises are weaker than same/adjacent-row separation, and coincide with
the permitted one-column original-interval overlap at row distance two.
No additional diagonal or cycle obstruction is used. -/
theorem three_horizontal_rods_deficit (Q : Nat) (hQ : 4 ≤ Q)
    (R0 R1 R2 : InteriorRod Q)
    (hr01 : R0.row ≤ R1.row) (hr12 : R1.row ≤ R2.row)
    (hg01 : R1.row ≤ R0.row + 2 →
      (Icc R0.left R0.right ∩ Icc R1.left R1.right).card ≤ 1)
    (hg02 : R2.row ≤ R0.row + 2 →
      (Icc R0.left R0.right ∩ Icc R2.left R2.right).card ≤ 1)
    (hg12 : R2.row ≤ R1.row + 2 →
      (Icc R1.left R1.right ∩ Icc R2.left R2.right).card ≤ 1)
    (V : Nat → Finset Nat)
    (hV : ∀ t ∈ Icc 1 (3 * Q), Spaced (V t) ∧ V t ⊆ Icc 3 (3 * Q + 1))
    (hs0 : R0.Excludes V) (hs1 : R1.Excludes V) (hs2 : R2.Excludes V) :
    (R0.right - R0.left) + (R1.right - R1.left) + (R2.right - R2.left) ≤
      (Icc 1 (3 * Q)).sum (fun t => Q - (V t).card) := by
  have hE (R : InteriorRod Q) : Ico R.left R.right ⊆ Icc 2 (3 * Q + 1) := by
    intro x hx
    have := mem_Ico.mp hx
    have := R.column_bounds
    simp only [mem_Icc]
    omega
  have hshadow (R : InteriorRod Q) (hs : R.Excludes V) :
      ∀ t ∈ Icc 1 (3 * Q), t ∈ Icc (R.row - 2) (R.row + 1) →
        ∀ v ∈ V t, ∀ x ∈ Ico R.left R.right, v + 1 < x ∨ x + 2 < v := by
    intro t ht htr v hv x hx
    have hxI := mem_Ico.mp hx
    have hvnot : v ∉ Icc (R.left - 1) (R.right + 1) :=
      fun hm => disjoint_left.mp (hs t ht htr) hv hm
    simp only [mem_Icc] at hvnot
    omega
  have h := interior_three_rod_deficit Q R0.row R1.row R2.row hQ
    R0.row_bounds.1 hr01 hr12 R2.row_bounds.2
    (Ico R0.left R0.right) (Ico R1.left R1.right) (Ico R2.left R2.right) V
    (hE R0) (hE R1) (hE R2)
    (fun hn => rod_edge_columns_disjoint _ _ _ _ (hg01 hn))
    (fun hn => rod_edge_columns_disjoint _ _ _ _ (hg02 hn))
    (fun hn => rod_edge_columns_disjoint _ _ _ _ (hg12 hn)) hV
    (hshadow R0 hs0) (hshadow R1 hs1) (hshadow R2 hs2)
  simpa only [Nat.card_Ico] using h

/-- Exact three-spacing capacity of a physical surviving-column set. This
definition uses a finite maximum, not a sum of per-rod losses. -/
def spacingCapacity (S : Finset Nat) : Nat :=
  (S.powerset.filter (fun V => ∀ x ∈ V, ∀ y ∈ V, x < y → x + 3 ≤ y)).sup Finset.card

theorem spacingCapacity_attained (S : Finset Nat) :
    ∃ V : Finset Nat, V ⊆ S ∧ Spaced V ∧ V.card = spacingCapacity S := by
  let C := S.powerset.filter (fun V => ∀ x ∈ V, ∀ y ∈ V, x < y → x + 3 ≤ y)
  have hC : C.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [C]
  obtain ⟨V, hV, heq⟩ := exists_mem_eq_sup C hC Finset.card
  have hmem := mem_filter.mp hV
  exact ⟨V, mem_powerset.mp hmem.1, hmem.2, heq.symm⟩

/-- The un-clipped shadow; intersection with the eligible interval is done
once, after taking the physical union of all active shadows. -/
def InteriorRod.shadow {Q : Nat} (R : InteriorRod Q) (t : Nat) : Finset Nat :=
  if t ∈ Icc (R.row - 2) (R.row + 1) then Icc (R.left - 1) (R.right + 1) else ∅

/-- Unconditional success of the exact joint-capacity certificate for three
interior rods satisfying the stated boundary and pairwise overlap geometry.
There are no vertical-column sets, chosen capacities, or deficit inequalities
among the premises: the capacities are computed from the physical union. -/
theorem three_horizontal_rods_certificate (Q : Nat) (hQ : 4 ≤ Q)
    (R0 R1 R2 : InteriorRod Q)
    (hr01 : R0.row ≤ R1.row) (hr12 : R1.row ≤ R2.row)
    (hg01 : R1.row ≤ R0.row + 2 →
      (Icc R0.left R0.right ∩ Icc R1.left R1.right).card ≤ 1)
    (hg02 : R2.row ≤ R0.row + 2 →
      (Icc R0.left R0.right ∩ Icc R2.left R2.right).card ≤ 1)
    (hg12 : R2.row ≤ R1.row + 2 →
      (Icc R1.left R1.right ∩ Icc R2.left R2.right).card ≤ 1) :
    (R0.right - R0.left) + (R1.right - R1.left) + (R2.right - R2.left) ≤
      (Icc 1 (3 * Q)).sum (fun t => Q - spacingCapacity
        (Icc 3 (3 * Q + 1) \ (R0.shadow t ∪ R1.shadow t ∪ R2.shadow t))) := by
  classical
  let S := fun t => Icc 3 (3 * Q + 1) \ (R0.shadow t ∪ R1.shadow t ∪ R2.shadow t)
  choose V hsub hspace hcard using fun t => spacingCapacity_attained (S t)
  have hV : ∀ t ∈ Icc 1 (3 * Q), Spaced (V t) ∧ V t ⊆ Icc 3 (3 * Q + 1) := by
    intro t _
    exact ⟨hspace t, (hsub t).trans sdiff_subset⟩
  have hnot (t x : Nat) (hx : x ∈ V t) : x ∉ R0.shadow t ∪ R1.shadow t ∪ R2.shadow t :=
    (mem_sdiff.mp (hsub t hx)).2
  have hs0 : R0.Excludes V := by
    intro t _ htr
    apply disjoint_left.mpr
    intro x hx hm
    apply hnot t x hx
    have hm' : x ∈ R0.shadow t := by simpa only [InteriorRod.shadow, if_pos htr] using hm
    exact mem_union_left _ (mem_union_left _ hm')
  have hs1 : R1.Excludes V := by
    intro t _ htr
    apply disjoint_left.mpr
    intro x hx hm
    apply hnot t x hx
    have hm' : x ∈ R1.shadow t := by simpa only [InteriorRod.shadow, if_pos htr] using hm
    exact mem_union_left _ (mem_union_right _ hm')
  have hs2 : R2.Excludes V := by
    intro t _ htr
    apply disjoint_left.mpr
    intro x hx hm
    apply hnot t x hx
    have hm' : x ∈ R2.shadow t := by simpa only [InteriorRod.shadow, if_pos htr] using hm
    exact mem_union_right _ hm'
  have h := three_horizontal_rods_deficit Q hQ R0 R1 R2 hr01 hr12 hg01 hg02 hg12 V hV hs0 hs1 hs2
  simpa only [hcard, S] using h

end GridGraphs.CarrierLayers.MixedPacking
