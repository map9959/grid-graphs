import GridGraphs.Geometry.StraightForcedComponents
import GridGraphs.Accounting.ComponentReduction
import GridGraphs.Geometry.GridBoundaryCycle

/-!
# Boundary runs in the `5 x 5` grid

Clockwise boundary positions, run counts, and omissions exclude the all-boundary
four-corner profile and locate the fifth omission when three runs remain.
-/

namespace GridGraphs.SmallDiagonalProof

open Finset SimpleGraph

def corners55 : Finset (GridVertex 5 5) :=
  Finset.univ.filter fun v =>
    (v.1.val = 0 ∨ v.1.val + 1 = 5) ∧
      (v.2.val = 0 ∨ v.2.val + 1 = 5)

def boundary55 : Finset (GridVertex 5 5) :=
  Finset.univ.filter fun v =>
    v.1.val = 0 ∨ v.1.val + 1 = 5 ∨
      v.2.val = 0 ∨ v.2.val + 1 = 5

def boundaryPosition55 (i : Fin 16) : GridBoundaryPosition 5 5 :=
  ⟨i.val, by simp [gridBoundaryLength]⟩

def boundaryVertex55 (i : Fin 16) : GridVertex 5 5 :=
  gridBoundaryVertex (m := 5) (n := 5) (by omega) (by omega)
    (boundaryPosition55 i)

/-- Boundary positions occupied by a forced set, in clockwise cyclic order. -/
def _root_.GridGraphs.boundaryForcedPositions55 (F : Finset (GridVertex 5 5)) : Finset (Fin 16) :=
  Finset.univ.filter fun i =>
    boundaryVertex55 i ∈ F

lemma mem_boundaryForcedPositions55 (F : Finset (GridVertex 5 5)) (i : Fin 16) :
    i ∈ boundaryForcedPositions55 F ↔ boundaryVertex55 i ∈ F := by
  simp only [boundaryForcedPositions55, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The path forest formed by the cyclic boundary runs of `F`. -/
def _root_.GridGraphs.boundaryForcedRunGraph55 (F : Finset (GridVertex 5 5)) :
    SimpleGraph (↑(boundaryForcedPositions55 F) : Set (Fin 16)) :=
  (cycleGraph 16).induce (↑(boundaryForcedPositions55 F) : Set (Fin 16))

/-- Number of cyclic boundary `F`-runs. -/
noncomputable def _root_.GridGraphs.boundaryForcedRunCount55 (F : Finset (GridVertex 5 5)) : Nat :=
  Fintype.card (boundaryForcedRunGraph55 F).ConnectedComponent

lemma boundaryPosition55_succ (i : Fin 16) :
    gridBoundarySucc (m := 5) (n := 5) (by omega) (by omega)
      (boundaryPosition55 i) = boundaryPosition55 (i + 1) := by
  apply Fin.ext
  rfl

/-- The clockwise boundary numbering embeds the abstract `16`-cycle in the
`5 x 5` grid. -/
def gridBoundaryCycleHom55 : cycleGraph 16 →g gridGraph 5 5 where
  toFun := boundaryVertex55
  map_rel' := by
    intro i j hij
    have hj : j = i - 1 ∨ j = i + 1 := by
      have hjmem : j ∈ (cycleGraph 16).neighborSet i := hij
      rw [cycleGraph_neighborSet] at hjmem
      simpa [eq_comm] using hjmem
    rcases hj with h | h
    · have hi : i = j + 1 := by
        rw [h]
        simp
      rw [hi]
      change (gridGraph 5 5).Adj (boundaryVertex55 (j + 1)) (boundaryVertex55 j)
      rw [boundaryVertex55, boundaryVertex55, ← boundaryPosition55_succ]
      exact (gridBoundaryVertex_succ_adj (m := 5) (n := 5)
        (by omega) (by omega) (boundaryPosition55 j)).symm
    · rw [h]
      change (gridGraph 5 5).Adj (boundaryVertex55 i) (boundaryVertex55 (i + 1))
      rw [boundaryVertex55, boundaryVertex55, ← boundaryPosition55_succ]
      exact gridBoundaryVertex_succ_adj (m := 5) (n := 5)
        (by omega) (by omega) (boundaryPosition55 i)

set_option maxHeartbeats 800000 in
lemma gridBoundaryCycleHom55_reflects_adj {i j : Fin 16}
    (hij : (gridGraph 5 5).Adj (boundaryVertex55 i) (boundaryVertex55 j)) :
    (cycleGraph 16).Adj i j := by
  rw [cycleGraph_adj']
  change adjacent 5 5 (boundaryVertex55 i) (boundaryVertex55 j) at hij
  unfold boundaryVertex55 gridBoundaryVertex boundaryPosition55 gridBoundaryLength adjacent at hij
  dsimp only at hij
  split_ifs at hij
  all_goals
    simp only [Fin.sub_def]
    rcases hij with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    rcases h' with h' | h'
  all_goals norm_num [Fin.mk.injEq] at *
  all_goals
    have hmod :
        (16 - j.val + i.val = 1 ∨ 16 - j.val + i.val = 17) ∨
        (16 - i.val + j.val = 1 ∨ 16 - i.val + j.val = 17) := by
      omega
    rcases hmod with (h | h) | (h | h) <;> simp [h]

/-- Inclusion of a cyclic boundary run into the ambient induced forced graph. -/
def _root_.GridGraphs.boundaryForcedRunToInducedHom55 (F : Finset (GridVertex 5 5)) :
    boundaryForcedRunGraph55 F →g
      (gridGraph 5 5).induce (↑F : Set (GridVertex 5 5)) where
  toFun i := ⟨gridBoundaryCycleHom55 i.1, by
    simpa [boundaryForcedPositions55, gridBoundaryCycleHom55] using i.2⟩
  map_rel' := by
    intro i j hij
    exact gridBoundaryCycleHom55.map_rel hij

/-- Ambient induced component containing a cyclic boundary run. -/
def _root_.GridGraphs.boundaryForcedRunAncestor55 (F : Finset (GridVertex 5 5))
    (C : (boundaryForcedRunGraph55 F).ConnectedComponent) :
    ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent :=
  C.map (boundaryForcedRunToInducedHom55 F)

lemma cycleGraph_sixteen_adj_not_both_odd {i j : Fin 16}
    (hij : (cycleGraph 16).Adj i j) :
    ¬(i.val % 2 = 1 ∧ j.val % 2 = 1) := by
  intro hodd
  have hj : j = i - 1 ∨ j = i + 1 := by
    have hjmem : j ∈ (cycleGraph 16).neighborSet i := hij
    rw [cycleGraph_neighborSet] at hjmem
    simpa [eq_comm] using hjmem
  have succ_not_both_odd (x : Fin 16)
      (hx : x.val % 2 = 1) (hsucc : (x + 1).val % 2 = 1) : False := by
    change ((x.val + 1) % 16) % 2 = 1 at hsucc
    by_cases hxlast : x.val + 1 < 16
    · rw [Nat.mod_eq_of_lt hxlast] at hsucc
      omega
    · have : x.val + 1 = 16 := by omega
      simp [this] at hsucc
  rcases hj with h | h
  · have hi : i = j + 1 := by rw [h]; simp
    rw [hi] at hodd
    exact succ_not_both_odd j hodd.2 hodd.1
  · rw [h] at hodd
    exact succ_not_both_odd i hodd.1 hodd.2

lemma boundaryForcedRunCount55_three_le_of_four_odd_omissions
    (F : Finset (GridVertex 5 5)) (Q : Finset (Fin 16))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hQcard : Q.card = 4)
    (hQomit : Q ⊆ (Finset.univ : Finset (Fin 16))
      \ boundaryForcedPositions55 F)
    (hQodd : ∀ q ∈ Q, q.val % 2 = 1) :
    3 ≤ boundaryForcedRunCount55 F := by
  classical
  let G := cycleGraph 16
  let P := boundaryForcedPositions55 F
  let A := forcedEdgeGraph G (↑Q : Set (Fin 16))
  let B := boundaryForcedRunGraph55 F
  have hdeg (i : Fin 16) : G.degree i = 2 := by
    dsimp [G]
    rw [cycleGraph_degree_two_le, Finset.card_pair]
    intro heq
    have hi : i = i + 2 := by
      have := congrArg (fun x => x + 1) heq
      simpa only [sub_add_cancel, add_assoc, show (1 : Fin 16) + 1 = 2 from rfl] using this
    have hzero : (0 : Fin 16) = 2 :=
      add_left_cancel (a := i) (by simpa only [add_zero] using hi)
    have := congrArg Fin.val hzero
    norm_num at this
  have hQinduced : (G.induce (↑Q : Set (Fin 16))).edgeFinset.card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    induction e using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at he
        exact cycleGraph_sixteen_adj_not_both_odd he
          ⟨hQodd i i.2, hQodd j j.2⟩
  have hAcard : A.edgeFinset.card = 8 := by
    have hsum := sum_degrees_finset_eq_forced_add_induced G Q
    rw [Finset.sum_congr rfl (fun i _ => hdeg i), hQinduced] at hsum
    simp [hQcard] at hsum
    exact hsum.symm
  let E := B.edgeFinset.map
    (Function.Embedding.subtype (↑P : Set (Fin 16))).sym2Map
  have hEcard : E.card = B.edgeFinset.card := by simp [E]
  have hEsub : E ⊆ G.edgeFinset := by
    intro e he
    simp only [E, Finset.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    induction e' using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at he' ⊢
        exact he'
  have hAsub : A.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at he ⊢
        exact he.1
  have hdisjoint : Disjoint A.edgeFinset E := by
    rw [Finset.disjoint_left]
    intro e heA heE
    induction e using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at heA
        simp only [E, Finset.mem_map] at heE
        obtain ⟨e', he', heq⟩ := heE
        induction e' using Sym2.inductionOn with
        | _ u v =>
            change s(u.1, v.1) = s(i, j) at heq
            rw [Sym2.eq_iff] at heq
            rw [SimpleGraph.mem_edgeFinset] at he'
            rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rcases heA.2 with hi | hj
              · exact (Finset.mem_sdiff.mp (hQomit hi)).2 u.2
              · exact (Finset.mem_sdiff.mp (hQomit hj)).2 v.2
            · rcases heA.2 with hi | hj
              · exact (Finset.mem_sdiff.mp (hQomit hi)).2 v.2
              · exact (Finset.mem_sdiff.mp (hQomit hj)).2 u.2
  have hGcard : G.edgeFinset.card = 16 := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    have hleft : (∑ i : Fin 16, G.degree i) = 32 := by
      simp [hdeg]
    rw [hleft] at hsum
    omega
  have hBedge : B.edgeFinset.card ≤ 8 := by
    have hunion : A.edgeFinset ∪ E ⊆ G.edgeFinset :=
      Finset.union_subset hAsub hEsub
    have hc := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdisjoint, hAcard, hEcard, hGcard] at hc
    omega
  have hBacyc : (boundaryForcedRunGraph55 F).IsAcyclic := by
    let f : B →g forcedEdgeGraph (gridGraph 5 5)
        (↑F : Set (GridVertex 5 5)) := {
      toFun := fun i => boundaryVertex55 i.1
      map_rel' := by
        intro i j hij
        have hiF : boundaryVertex55 i.1 ∈ F := by
          simpa [P, B, boundaryForcedRunGraph55,
            boundaryForcedPositions55] using i.2
        exact ⟨gridBoundaryCycleHom55.map_rel hij, Or.inl hiF⟩ }
    exact hacyc.comap f (fun i j hij => Subtype.ext
      (gridBoundaryVertex_injective (m := 5) (n := 5)
        (by omega) (by omega) hij))
  let : Fintype (boundaryForcedRunGraph55 F).ConnectedComponent :=
    SetLike.instFintype
  have hledger := hBacyc.card_edgeFinset_add_card_connectedComponent
  have hcomponentInstances :
      @Fintype.card (boundaryForcedRunGraph55 F).ConnectedComponent
          (boundaryForcedRunGraph55 F).instFintypeConnectedComponent =
        @Fintype.card (boundaryForcedRunGraph55 F).ConnectedComponent this :=
    @Fintype.card_congr _ _
      (boundaryForcedRunGraph55 F).instFintypeConnectedComponent this (Equiv.refl _)
  have hverts : Fintype.card
      (↑(boundaryForcedPositions55 F) : Set (Fin 16)) = 11 := by
    simpa using hPcard
  dsimp [B] at hBedge
  rw [hverts] at hledger
  rw [hcomponentInstances] at hledger
  dsimp [B] at hledger
  have hledger' :
      (boundaryForcedRunGraph55 F).edgeFinset.card +
        Fintype.card (boundaryForcedRunGraph55 F).ConnectedComponent = 11 := by
    exact hledger
  have hc : 3 ≤ Fintype.card
      (boundaryForcedRunGraph55 F).ConnectedComponent := by
    omega
  simpa only [boundaryForcedRunCount55] using hc

/-- If the lower bound on cyclic boundary runs is sharp, the fifth omission is
an even side midpoint, flanked by two of the four selected odd omissions. -/
theorem _root_.GridGraphs.fifth_boundary_omission_is_side_midpoint_of_three_runs
    (F : Finset (GridVertex 5 5)) (Q : Finset (Fin 16))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hQcard : Q.card = 4)
    (hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F)
    (hQodd : ∀ q ∈ Q, q.val % 2 = 1)
    (hcorners : ∀ i : Fin 16, i.val % 4 = 0 →
      i ∈ boundaryForcedPositions55 F)
    (hruns : boundaryForcedRunCount55 F = 3) :
    ∃ e : Fin 16,
      e ∈ (Finset.univ : Finset (Fin 16)) \ boundaryForcedPositions55 F ∧
      e ∉ Q ∧ e.val ∈ ({2, 6, 10, 14} : Finset Nat) ∧
      e - 1 ∈ Q ∧ e + 1 ∈ Q := by
  classical
  let G := cycleGraph 16
  let P := boundaryForcedPositions55 F
  let O : Finset (Fin 16) := Finset.univ \ P
  let A := forcedEdgeGraph G (↑Q : Set (Fin 16))
  let B := boundaryForcedRunGraph55 F
  have hOcard : O.card = 5 := by
    simp [O, P, Finset.card_sdiff, hPcard]
  have hQO : Q ⊆ O := hQomit
  have hdiffCard : (O \ Q).card = 1 := by
    rw [Finset.card_sdiff_of_subset hQO, hOcard, hQcard]
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hdiffCard
  have heO : e ∈ O := by
    have : e ∈ O \ Q := by simp [he]
    exact (Finset.mem_sdiff.mp this).1
  have heQ : e ∉ Q := by
    have : e ∈ O \ Q := by simp [he]
    exact (Finset.mem_sdiff.mp this).2
  have hdeg (i : Fin 16) : G.degree i = 2 := by
    dsimp [G]
    rw [cycleGraph_degree_two_le, Finset.card_pair]
    intro heq
    have hi : i = i + 2 := by
      have := congrArg (fun x => x + 1) heq
      simpa only [sub_add_cancel, add_assoc, show (1 : Fin 16) + 1 = 2 from rfl] using this
    have hzero : (0 : Fin 16) = 2 :=
      add_left_cancel (a := i) (by simpa only [add_zero] using hi)
    have := congrArg Fin.val hzero
    norm_num at this
  have hQinduced : (G.induce (↑Q : Set (Fin 16))).edgeFinset.card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at hedge
        exact cycleGraph_sixteen_adj_not_both_odd hedge
          ⟨hQodd i i.2, hQodd j j.2⟩
  have hAcard : A.edgeFinset.card = 8 := by
    have hsum := sum_degrees_finset_eq_forced_add_induced G Q
    rw [Finset.sum_congr rfl (fun i _ => hdeg i), hQinduced] at hsum
    simp [hQcard] at hsum
    exact hsum.symm
  have hBacyc : B.IsAcyclic := by
    let f : B →g forcedEdgeGraph (gridGraph 5 5)
        (↑F : Set (GridVertex 5 5)) := {
      toFun := fun i => boundaryVertex55 i.1
      map_rel' := by
        intro i j hij
        have hiF : boundaryVertex55 i.1 ∈ F := by
          simpa [P, B, boundaryForcedRunGraph55,
            boundaryForcedPositions55] using i.2
        exact ⟨gridBoundaryCycleHom55.map_rel hij, Or.inl hiF⟩ }
    exact hacyc.comap f (fun i j hij => Subtype.ext
      (gridBoundaryVertex_injective (m := 5) (n := 5)
        (by omega) (by omega) hij))
  let : Fintype B.ConnectedComponent := SetLike.instFintype
  have hledger := hBacyc.card_edgeFinset_add_card_connectedComponent
  have hcomponentInstances :
      @Fintype.card B.ConnectedComponent B.instFintypeConnectedComponent =
        @Fintype.card B.ConnectedComponent this :=
    @Fintype.card_congr _ _ B.instFintypeConnectedComponent this (Equiv.refl _)
  have hverts : Fintype.card (↑P : Set (Fin 16)) = 11 := by
    simpa [P] using hPcard
  have hcomponents : Fintype.card B.ConnectedComponent = 3 := by
    simpa [B, boundaryForcedRunCount55] using hruns
  have hBcard : B.edgeFinset.card = 8 := by
    rw [hverts, hcomponentInstances, hcomponents] at hledger
    omega
  let E := B.edgeFinset.map
    (Function.Embedding.subtype (↑P : Set (Fin 16))).sym2Map
  have hEcard : E.card = 8 := by
    rw [show E.card = B.edgeFinset.card by simp [E], hBcard]
  have hEsub : E ⊆ G.edgeFinset := by
    intro edge hedge
    simp only [E, Finset.mem_map] at hedge
    obtain ⟨edge', hedge', rfl⟩ := hedge
    induction edge' using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at hedge' ⊢
        exact hedge'
  have hAsub : A.edgeFinset ⊆ G.edgeFinset := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at hedge ⊢
        exact hedge.1
  have hdisjoint : Disjoint A.edgeFinset E := by
    rw [Finset.disjoint_left]
    intro edge hedgeA hedgeE
    induction edge using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at hedgeA
        simp only [E, Finset.mem_map] at hedgeE
        obtain ⟨edge', hedge', hedgeq⟩ := hedgeE
        induction edge' using Sym2.inductionOn with
        | _ u v =>
            change s(u.1, v.1) = s(i, j) at hedgeq
            rw [Sym2.eq_iff] at hedgeq
            rcases hedgeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              rcases hedgeA.2 with hi | hj
            · exact (Finset.mem_sdiff.mp (hQomit hi)).2 u.2
            · exact (Finset.mem_sdiff.mp (hQomit hj)).2 v.2
            · exact (Finset.mem_sdiff.mp (hQomit hi)).2 v.2
            · exact (Finset.mem_sdiff.mp (hQomit hj)).2 u.2
  have hGcard : G.edgeFinset.card = 16 := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    have hleft : (∑ i : Fin 16, G.degree i) = 32 := by simp [hdeg]
    rw [hleft] at hsum
    omega
  have hunion : A.edgeFinset ∪ E = G.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hAsub hEsub)
    rw [Finset.card_union_of_disjoint hdisjoint, hAcard, hEcard, hGcard]
  have hneighbor {j : Fin 16} (hej : G.Adj e j) : j ∈ Q := by
    have hedgeG : s(e, j) ∈ G.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hej
    rw [← hunion] at hedgeG
    rcases Finset.mem_union.mp hedgeG with hedgeA | hedgeE
    · rw [SimpleGraph.mem_edgeFinset] at hedgeA
      exact hedgeA.2.resolve_left heQ
    · simp only [E, Finset.mem_map] at hedgeE
      obtain ⟨edge', hedge', hedgeq⟩ := hedgeE
      induction edge' using Sym2.inductionOn with
      | _ u v =>
          change s(u.1, v.1) = s(e, j) at hedgeq
          rw [Sym2.eq_iff] at hedgeq
          rcases hedgeq with ⟨hue, _⟩ | ⟨_, hve⟩
          · exact ((Finset.mem_sdiff.mp heO).2 (hue ▸ u.2)).elim
          · exact ((Finset.mem_sdiff.mp heO).2 (hve ▸ v.2)).elim
  have hprev : e - 1 ∈ Q := hneighbor (by
    rw [cycleGraph_adj]
    left
    simp)
  have hnext : e + 1 ∈ Q := hneighbor (by
    rw [cycleGraph_adj]
    right
    simp)
  have heEven : e.val % 2 = 0 := by
    have hp := hQodd (e - 1) hprev
    have hn := hQodd (e + 1) hnext
    simp only [Fin.sub_def, Fin.add_def] at hp hn
    norm_num at hp hn
    omega
  have heNotCorner : e.val % 4 ≠ 0 := by
    intro heCorner
    exact (Finset.mem_sdiff.mp heO).2 (hcorners e heCorner)
  have heMid : e.val ∈ ({2, 6, 10, 14} : Finset Nat) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact ⟨e, heO, heQ, heMid, hprev, hnext⟩

lemma corners55_card : corners55.card = 4 := by
  let endpoints : Finset (Fin 5) := {0, 4}
  have hcorners : corners55 = endpoints ×ˢ endpoints := by
    ext v
    rw [Finset.mem_product]
    simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and,
      endpoints, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro ⟨hr, hc⟩
    · constructor
      · rcases hr with h | h
        · left; apply Fin.ext; omega
        · right; apply Fin.ext; omega
      · rcases hc with h | h
        · left; apply Fin.ext; omega
        · right; apply Fin.ext; omega
    · constructor
      · rcases hr with h | h
        · left; simp [h]
        · right; have := congrArg Fin.val h; norm_num at this ⊢; omega
      · rcases hc with h | h
        · left; simp [h]
        · right; have := congrArg Fin.val h; norm_num at this ⊢; omega
  have hendpoints : endpoints.card = 2 := by
    rw [Finset.card_pair]
    intro h
    have := congrArg Fin.val h
    norm_num at this
  rw [hcorners, Finset.card_product, hendpoints]

lemma cycleGraph_sixteen_not_isAcyclic :
    ¬(cycleGraph 16).IsAcyclic := by
  intro hacyc
  have htree : (cycleGraph 16).IsTree := ⟨cycleGraph_connected, hacyc⟩
  have hcard := htree.card_edgeFinset
  have hdeg := (cycleGraph 16).sum_degrees_eq_twice_card_edges
  have htwo : ∀ i : Fin 16, (cycleGraph 16).degree i = 2 := by
    intro i
    rw [cycleGraph_degree_two_le, Finset.card_pair]
    intro heq
    have hi : i = i + 2 := by
      have := congrArg (fun x => x + 1) heq
      simpa only [sub_add_cancel, add_assoc, show (1 : Fin 16) + 1 = 2 from rfl] using this
    have hzero : (0 : Fin 16) = 2 :=
      add_left_cancel (a := i) (by simpa only [add_zero] using hi)
    have := congrArg Fin.val hzero
    norm_num at this
  rw [Finset.sum_congr rfl (fun i _ => htwo i)] at hdeg
  norm_num at hcard hdeg
  omega

/-- The twelve-vertex profile supported entirely on the boundary and containing
all four corners is impossible.  At every forced corner, one of its two
boundary neighbors must be omitted.  These four omissions are distinct and
odd-numbered; cardinality then makes every omission odd, so every edge of the
boundary cycle is forced. -/
theorem _root_.GridGraphs.forced_five_five_twelve_boundary_four_corners_impossible
    (F : Finset (GridVertex 5 5))
    (hboundary : (F ∩ boundary55).card = 12)
    (hcornersCard : (F ∩ corners55).card = 4)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic) : False := by
  classical
  let P := boundaryForcedPositions55 F
  let O : Finset (Fin 16) := Finset.univ \ P
  have hcorners : corners55 ⊆ F := by
    have hinter : F ∩ corners55 = corners55 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hcornersCard, corners55_card])
    intro v hv
    have : v ∈ F ∩ corners55 := by simpa [hinter] using hv
    exact (Finset.mem_inter.mp this).1
  have himage : P.image boundaryVertex55 = F ∩ boundary55 := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      have hiF : boundaryVertex55 i ∈ F := by
        simpa [P, boundaryForcedPositions55] using hi
      exact Finset.mem_inter.mpr ⟨hiF, by
        simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [IsGridBoundary, boundaryVertex55] using
          (gridBoundaryVertex_isBoundary (m := 5) (n := 5)
            (by omega) (by omega) (boundaryPosition55 i))⟩
    · intro hv
      have hv' := Finset.mem_inter.mp hv
      have hvB : IsGridBoundary v := by
        simpa [boundary55, IsGridBoundary] using hv'.2
      obtain ⟨i, hi⟩ := exists_gridBoundaryPosition (m := 5) (n := 5)
        (by omega) (by omega) v hvB
      refine Finset.mem_image.mpr ⟨⟨i.val, by simpa [gridBoundaryLength] using i.isLt⟩,
        ?_, ?_⟩
      · simpa [P, mem_boundaryForcedPositions55, boundaryVertex55,
          boundaryPosition55, hi] using hv'.1
      · simpa [boundaryVertex55, boundaryPosition55] using hi
  have hPcard : P.card = 12 := by
    have hinj : Function.Injective boundaryVertex55 := by
      intro i j hij
      exact gridBoundaryVertex_injective (m := 5) (n := 5)
        (by omega) (by omega) hij
    rw [← hboundary, ← himage, Finset.card_image_of_injective _ hinj]
  have hOcard : O.card = 4 := by
    calc
      O.card = (Finset.univ : Finset (Fin 16)).card -
          (P ∩ Finset.univ).card := by simp only [O, Finset.card_sdiff]
      _ = 4 := by simp [hPcard]
  have hcorner (r c : Fin 5)
      (hr : r.val = 0 ∨ r.val + 1 = 5)
      (hc : c.val = 0 ∨ c.val + 1 = 5) : (r, c) ∈ F := by
    apply hcorners
    simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr, hc⟩
  have htriple00 := (grid_cell_forced_triples_free (F := (↑F : Set _))
    (⟨0, by omega⟩ : Fin (5 - 1)) (⟨0, by omega⟩ : Fin (5 - 1)) hacyc).2.2.2
  have htriple04 := (grid_cell_forced_triples_free (F := (↑F : Set _))
    (⟨0, by omega⟩ : Fin (5 - 1)) (⟨3, by omega⟩ : Fin (5 - 1)) hacyc).1
  have htriple44 := (grid_cell_forced_triples_free (F := (↑F : Set _))
    (⟨3, by omega⟩ : Fin (5 - 1)) (⟨3, by omega⟩ : Fin (5 - 1)) hacyc).2.1
  have htriple40 := (grid_cell_forced_triples_free (F := (↑F : Set _))
    (⟨3, by omega⟩ : Fin (5 - 1)) (⟨0, by omega⟩ : Fin (5 - 1)) hacyc).2.2.1
  have hq0 : ∃ q ∈ ({15, 1} : Finset (Fin 16)), q ∈ O := by
    by_cases h15 : boundaryVertex55 15 ∈ F
    · refine ⟨1, by simp, ?_⟩
      simp only [O, Finset.mem_sdiff, Finset.mem_univ, true_and, P,
        boundaryForcedPositions55, Finset.mem_filter]
      intro h1
      apply htriple00
      simpa [cell10, cell00, cell01, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using
        ⟨h15, hcorner 0 0 (Or.inl rfl) (Or.inl rfl), h1⟩
    · exact ⟨15, by simp, by simpa [O, P, boundaryForcedPositions55]⟩
  have hq1 : ∃ q ∈ ({3, 5} : Finset (Fin 16)), q ∈ O := by
    by_cases h3 : boundaryVertex55 3 ∈ F
    · refine ⟨5, by simp, ?_⟩
      simp only [O, Finset.mem_sdiff, Finset.mem_univ, true_and, P,
        boundaryForcedPositions55, Finset.mem_filter]
      intro h5
      apply htriple04
      simpa [cell00, cell01, cell11, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using
        ⟨h3, hcorner 0 4 (Or.inl rfl) (Or.inr (by omega)), h5⟩
    · exact ⟨3, by simp, by simpa [O, P, boundaryForcedPositions55]⟩
  have hq2 : ∃ q ∈ ({7, 9} : Finset (Fin 16)), q ∈ O := by
    by_cases h7 : boundaryVertex55 7 ∈ F
    · refine ⟨9, by simp, ?_⟩
      simp only [O, Finset.mem_sdiff, Finset.mem_univ, true_and, P,
        boundaryForcedPositions55, Finset.mem_filter]
      intro h9
      apply htriple44
      simpa [cell01, cell11, cell10, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using
        ⟨h7, hcorner 4 4 (Or.inr (by omega)) (Or.inr (by omega)), h9⟩
    · exact ⟨7, by simp, by simpa [O, P, boundaryForcedPositions55]⟩
  have hq3 : ∃ q ∈ ({11, 13} : Finset (Fin 16)), q ∈ O := by
    by_cases h11 : boundaryVertex55 11 ∈ F
    · refine ⟨13, by simp, ?_⟩
      simp only [O, Finset.mem_sdiff, Finset.mem_univ, true_and, P,
        boundaryForcedPositions55, Finset.mem_filter]
      intro h13
      apply htriple40
      simpa [cell11, cell10, cell00, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using
        ⟨h11, hcorner 4 0 (Or.inr (by omega)) (Or.inl rfl), h13⟩
    · exact ⟨11, by simp, by simpa [O, P, boundaryForcedPositions55]⟩
  obtain ⟨q0, hq0p, hq0O⟩ := hq0
  obtain ⟨q1, hq1p, hq1O⟩ := hq1
  obtain ⟨q2, hq2p, hq2O⟩ := hq2
  obtain ⟨q3, hq3p, hq3O⟩ := hq3
  let Q : Finset (Fin 16) := {q0, q1, q2, q3}
  have hQcard : Q.card = 4 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq0p hq1p hq2p hq3p
    simp [Q]
    aesop
  have hQO : Q ⊆ O := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hq0O
    · exact hq1O
    · exact hq2O
    · exact hq3O
  have hOQ : O = Q :=
    (Finset.eq_of_subset_of_card_le hQO (by rw [hOcard, hQcard])).symm
  have hq0odd : q0.val % 2 = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq0p
    rcases hq0p with rfl | rfl <;> norm_num
  have hq1odd : q1.val % 2 = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq1p
    rcases hq1p with rfl | rfl <;> norm_num
  have hq2odd : q2.val % 2 = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq2p
    rcases hq2p with rfl | rfl <;> norm_num
  have hq3odd : q3.val % 2 = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq3p
    rcases hq3p with rfl | rfl <;> norm_num
  have hOodd {i : Fin 16} (hi : i ∈ O) : i.val % 2 = 1 := by
    rw [hOQ] at hi
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hq0odd
    · exact hq1odd
    · exact hq2odd
    · exact hq3odd
  have hedgeForced {i j : Fin 16} (hij : (cycleGraph 16).Adj i j) :
      boundaryVertex55 i ∈ F ∨ boundaryVertex55 j ∈ F := by
    by_contra hnot
    push Not at hnot
    have hiO : i ∈ O := by simp [O, P, boundaryForcedPositions55, hnot.1]
    have hjO : j ∈ O := by simp [O, P, boundaryForcedPositions55, hnot.2]
    have hiOdd := hOodd hiO
    have hjOdd := hOodd hjO
    have hj : j = i - 1 ∨ j = i + 1 := by
      have := show j ∈ (cycleGraph 16).neighborSet i from hij
      rw [cycleGraph_neighborSet] at this
      simpa [eq_comm] using this
    have succ_not_both_odd (x : Fin 16)
        (hxOdd : x.val % 2 = 1) (hyOdd : (x + 1).val % 2 = 1) : False := by
      change ((x.val + 1) % 16) % 2 = 1 at hyOdd
      by_cases hx : x.val + 1 < 16
      · rw [Nat.mod_eq_of_lt hx] at hyOdd
        omega
      · have hxlast : x.val + 1 = 16 := by omega
        simp [hxlast] at hyOdd
    rcases hj with h | h
    · have hi : i = j + 1 := by rw [h]; simp
      rw [hi] at hiOdd
      exact succ_not_both_odd j hjOdd hiOdd
    · rw [h] at hjOdd
      exact succ_not_both_odd i hiOdd hjOdd
  let f : cycleGraph 16 →g forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5)) := {
    toFun := boundaryVertex55
    map_rel' := by
      intro i j hij
      exact ⟨gridBoundaryCycleHom55.map_rel hij, hedgeForced hij⟩ }
  apply cycleGraph_sixteen_not_isAcyclic
  exact hacyc.comap f (gridBoundaryVertex_injective
    (m := 5) (n := 5) (by omega) (by omega))

lemma boundaryForcedPositions55_card_eq_boundary_inter
    (F : Finset (GridVertex 5 5)) :
    (boundaryForcedPositions55 F).card = (F ∩ boundary55).card := by
  have himage : (boundaryForcedPositions55 F).image boundaryVertex55 =
      F ∩ boundary55 := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_inter.mpr ⟨by
        simpa [boundaryForcedPositions55] using hi, by
        simpa [boundary55, IsGridBoundary, boundaryVertex55] using
          gridBoundaryVertex_isBoundary (m := 5) (n := 5)
            (by omega) (by omega) (boundaryPosition55 i)⟩
    · intro hv
      have hv' := Finset.mem_inter.mp hv
      have hvB : IsGridBoundary v := by
        simpa [boundary55, IsGridBoundary] using hv'.2
      obtain ⟨i, hi⟩ := exists_gridBoundaryPosition (m := 5) (n := 5)
        (by omega) (by omega) v hvB
      let j : Fin 16 := ⟨i.val, by simpa [gridBoundaryLength] using i.isLt⟩
      exact Finset.mem_image.mpr ⟨j, by
        simpa [mem_boundaryForcedPositions55, boundaryVertex55,
          boundaryPosition55, j, hi] using hv'.1, by
        simpa [boundaryVertex55, boundaryPosition55, j] using hi⟩
  rw [← himage, Finset.card_image_of_injective]
  intro i j hij
  exact gridBoundaryVertex_injective (m := 5) (n := 5)
    (by omega) (by omega) hij

end GridGraphs.SmallDiagonalProof
