import GridGraphs.ResidueZeroTransitions

/-!
# Local frontier propagation for the residue-zero construction

The statements here are deliberately local: no classification theorem about
adjacent entries of `phaseRows` is imported.  An ordinary row propagates a
connected outer dual face row to the face row that it shares with its neighbour.
For a seam followed by an ordinary row the same statement is used upside down.
-/

namespace GridGraphs

open SimpleGraph

/-- Every face in one row reaches every face in another row.  Taking the two
rows equal says that the face-row frontier is connected. -/
def DualFaceRowsAttached {V : Type*} (G : SimpleGraph V) {n : Nat}
    (upper lower : Fin n → V) : Prop :=
  ∀ c d, G.Reachable (upper c) (lower d)

/-- The six local transition shapes.  This is intentionally independent of the
global word `phaseRows`. -/
inductive LocalPhaseTransition (k : Nat) : PhaseRow → PhaseRow → Prop where
  | ordinaryPred (a : Nat) (ha0 : 0 < a) (ha : a < k) :
      LocalPhaseTransition k (.ordinary a) (.ordinary (a - 1))
  | ordinarySucc (a : Nat) (ha : a + 1 < k) :
      LocalPhaseTransition k (.ordinary a) (.ordinary (a + 1))
  | ordinarySeamSame (a : Nat) (ha : a < k) :
      LocalPhaseTransition k (.ordinary a) (.seam a)
  | ordinarySeamSucc (a : Nat) (ha : a + 1 < k) :
      LocalPhaseTransition k (.ordinary a) (.seam (a + 1))
  | seamOrdinaryPred (a : Nat) (ha0 : 0 < a) (ha : a < k) :
      LocalPhaseTransition k (.seam a) (.ordinary (a - 1))
  | seamOrdinarySame (a : Nat) (ha : a < k) :
      LocalPhaseTransition k (.seam a) (.ordinary a)

/-- Abstract one-dimensional frontier lemma.  The paired columns are joined by
the common residue-one backbone.  Each intervening face is joined either to
the pair on its left or to the pair on its right. -/
private theorem attach_all_columns {V : Type*} {G : SimpleGraph V} {k : Nat}
    (hk : 1 ≤ k) (outer middle : Fin (3 * k - 1) → V)
    (houter : DualFaceRowsAttached G outer outer)
    (hpair : ∀ q (hq : q < k),
      (G.Reachable (outer ⟨3 * q, by omega⟩) (middle ⟨3 * q, by omega⟩) ∨
        G.Reachable (outer ⟨3 * q + 1, by omega⟩) (middle ⟨3 * q + 1, by omega⟩)) ∧
      G.Adj (middle ⟨3 * q, by omega⟩) (middle ⟨3 * q + 1, by omega⟩))
    (hgap : ∀ q (hq : q + 1 < k),
      (G.Reachable (outer ⟨3 * q + 1, by omega⟩) (middle ⟨3 * q + 1, by omega⟩) ∧
        G.Adj (middle ⟨3 * q + 1, by omega⟩) (middle ⟨3 * q + 2, by omega⟩)) ∨
      (G.Reachable (outer ⟨3 * (q + 1), by omega⟩) (middle ⟨3 * (q + 1), by omega⟩) ∧
        G.Adj (middle ⟨3 * q + 2, by omega⟩) (middle ⟨3 * (q + 1), by omega⟩))) :
    DualFaceRowsAttached G outer middle := by
  intro c d
  let q := d.val / 3
  have hmod : d.val % 3 < 3 := Nat.mod_lt _ (by omega)
  have hd : d.val = 3 * q + d.val % 3 := by
    dsimp [q]
    omega
  interval_cases hm : d.val % 3
  · have hq : q < k := by omega
    have hd' : d = ⟨3 * q, by omega⟩ := Fin.ext (by simp; omega)
    rw [hd']
    rcases (hpair q hq).1 with h | h
    · exact (houter c ⟨3 * q, by omega⟩).trans h
    · exact (houter c ⟨3 * q + 1, by omega⟩).trans
        (h.trans (hpair q hq).2.symm.reachable)
  · have hq : q < k := by omega
    have hd' : d = ⟨3 * q + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [hd']
    rcases (hpair q hq).1 with h | h
    · exact (houter c ⟨3 * q, by omega⟩).trans
        (h.trans (hpair q hq).2.reachable)
    · exact (houter c ⟨3 * q + 1, by omega⟩).trans h
  · have hq : q + 1 < k := by omega
    have hd' : d = ⟨3 * q + 2, by omega⟩ := Fin.ext (by simp; omega)
    rw [hd']
    rcases hgap q hq with h | h
    · exact (houter c ⟨3 * q + 1, by omega⟩).trans
        (h.1.trans h.2.reachable)
    · exact (houter c ⟨3 * (q + 1), by omega⟩).trans
        (h.1.trans h.2.symm.reachable)

private theorem ordinary_row_frontier {V : Type*} {G : SimpleGraph V}
    {k a : Nat} (hk : 1 ≤ k) (ha : a < k)
    (top bottom : PhaseRow) (outer middle : Fin (3 * k - 1) → V)
    (houter : DualFaceRowsAttached G outer outer)
    (hrun : ∀ c (hc : c < 3 * k - 1),
      PhaseOccupied k (.ordinary a) c → PhaseOccupied k (.ordinary a) (c + 1) →
        G.Adj (outer ⟨c, hc⟩) (middle ⟨c, hc⟩))
    (hcommon : ∀ c (hc0 : 0 < c) (hc : c < 3 * k - 1),
      CommonPhaseColumn k top bottom c →
        G.Adj (middle ⟨c - 1, by omega⟩) (middle ⟨c, hc⟩))
    (hbackbone : ∀ q (hq : q < k),
      CommonPhaseColumn k top bottom (3 * q + 1))
    (hgaps : ∀ q (hq : q + 1 < k),
      (q ≤ a ∧ CommonPhaseColumn k top bottom (3 * q + 2)) ∨
      (a < q + 1 ∧ CommonPhaseColumn k top bottom (3 * (q + 1)))) :
    DualFaceRowsAttached G outer middle := by
  apply attach_all_columns hk outer middle houter
  · intro q hq
    constructor
    · by_cases hqa : q ≤ a
      · exact Or.inr (hrun (3 * q + 1) (by omega)
          (ordinary_left_run ha hq hqa).1 (ordinary_left_run ha hq hqa).2).reachable
      · exact Or.inl (hrun (3 * q) (by omega)
          (ordinary_right_run ha hq (by omega)).1
          (ordinary_right_run ha hq (by omega)).2).reachable
    · exact hcommon (3 * q + 1) (by omega) (by omega) (hbackbone q hq)
  · intro q hq
    rcases hgaps q hq with h | h
    · exact Or.inl ⟨
        (hrun (3 * q + 1) (by omega)
          (ordinary_left_run ha (by omega) h.1).1
          (ordinary_left_run ha (by omega) h.1).2).reachable,
        hcommon (3 * q + 2) (by omega) (by omega) h.2⟩
    · exact Or.inr ⟨
        (hrun (3 * (q + 1)) (by omega)
          (ordinary_right_run ha (by omega) h.1).1
          (ordinary_right_run ha (by omega) h.1).2).reachable,
        hcommon (3 * (q + 1)) (by omega) (by omega) h.2⟩

private theorem ordinary_top_transition_frontier (k : Nat) (hk : 7 ≤ k)
    (i : Nat) (hi : i + 1 < (phaseRows k).length) (a : Nat) (ha : a < k)
    (bottom : PhaseRow)
    (htop : (phaseRows k)[i]'(by omega) = .ordinary a)
    (hbottom : (phaseRows k)[i + 1]'hi = bottom)
    (hgaps : ∀ q (hq : q + 1 < k),
      (q ≤ a ∧ CommonPhaseColumn k (.ordinary a) bottom (3 * q + 2)) ∨
      (a < q + 1 ∧ CommonPhaseColumn k (.ordinary a) bottom (3 * (q + 1))))
    (houter : DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
      (fun c => .cell ⟨i + 1, by rw [phaseRows_length k hk] at hi; omega⟩ c)
      (fun c => .cell ⟨i + 1, by rw [phaseRows_length k hk] at hi; omega⟩ c)) :
    DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
      (fun c => .cell ⟨i + 1, by rw [phaseRows_length k hk] at hi; omega⟩ c)
      (fun c => .cell ⟨i + 2, by rw [phaseRows_length k hk] at hi; omega⟩ c) := by
  apply ordinary_row_frontier (by omega) ha (.ordinary a) bottom _ _ houter
  · intro c hc hc₁ hc₂
    have hc₁' : PhaseOccupied k ((phaseRows k)[i]'(by omega)) c := by
      rw [htop]
      exact hc₁
    have hc₂' : PhaseOccupied k ((phaseRows k)[i]'(by omega)) (c + 1) := by
      rw [htop]
      exact hc₂
    rcases hc₁' with ⟨j₁, hj₁⟩
    rcases hc₂' with ⟨j₂, hj₂⟩
    exact horizontal_uu_dual_cells_adj (uResidueZero k hk) (i + 2) c
      (by omega) (by rw [phaseRows_length k hk] at hi; omega) hc
      (by simpa [hj₁] using phase_vertex_mem_uResidueZero k hk ⟨i, by omega⟩ j₁)
      (by simpa [hj₂] using phase_vertex_mem_uResidueZero k hk ⟨i, by omega⟩ j₂)
  · intro c hc0 hc hcommon
    apply consecutive_phase_common_column_dual_adj k hk i hi c hc0 hc
    simpa [htop, hbottom] using hcommon
  · intro q hq
    exact commonPhaseColumn_backbone hq
  · exact hgaps

private theorem ordinary_bottom_transition_frontier (k : Nat) (hk : 7 ≤ k)
    (i : Nat) (hi : i + 1 < (phaseRows k).length) (a : Nat) (ha : a < k)
    (top : PhaseRow)
    (htop : (phaseRows k)[i]'(by omega) = top)
    (hbottom : (phaseRows k)[i + 1]'hi = .ordinary a)
    (hgaps : ∀ q (hq : q + 1 < k),
      (q ≤ a ∧ CommonPhaseColumn k top (.ordinary a) (3 * q + 2)) ∨
      (a < q + 1 ∧ CommonPhaseColumn k top (.ordinary a) (3 * (q + 1))))
    (houter : DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
      (fun c => .cell ⟨i + 3, by rw [phaseRows_length k hk] at hi; omega⟩ c)
      (fun c => .cell ⟨i + 3, by rw [phaseRows_length k hk] at hi; omega⟩ c)) :
    DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
      (fun c => .cell ⟨i + 3, by rw [phaseRows_length k hk] at hi; omega⟩ c)
      (fun c => .cell ⟨i + 2, by rw [phaseRows_length k hk] at hi; omega⟩ c) := by
  apply ordinary_row_frontier (by omega) ha top (.ordinary a) _ _ houter
  · intro c hc hc₁ hc₂
    have hc₁' : PhaseOccupied k ((phaseRows k)[i + 1]'hi) c := by
      rw [hbottom]
      exact hc₁
    have hc₂' : PhaseOccupied k ((phaseRows k)[i + 1]'hi) (c + 1) := by
      rw [hbottom]
      exact hc₂
    rcases hc₁' with ⟨j₁, hj₁⟩
    rcases hc₂' with ⟨j₂, hj₂⟩
    exact (horizontal_uu_dual_cells_adj (uResidueZero k hk) (i + 3) c
      (by omega) (by rw [phaseRows_length k hk] at hi; omega) hc
      (by simpa [hj₁] using phase_vertex_mem_uResidueZero k hk ⟨i + 1, hi⟩ j₁)
      (by simpa [hj₂] using phase_vertex_mem_uResidueZero k hk ⟨i + 1, hi⟩ j₂)).symm
  · intro c hc0 hc hcommon
    exact consecutive_phase_common_column_dual_adj k hk i hi c hc0 hc
      (by simpa [htop, hbottom] using hcommon)
  · intro q hq
    exact commonPhaseColumn_backbone hq
  · exact hgaps

/-- A local transition propagates connectedness from the outer side of its
ordinary row to the shared frontier.  Thus the first four constructors work
top-to-bottom, while the two seam-first constructors work bottom-to-top. -/
theorem localPhaseTransition_frontier_attached (k : Nat) (hk : 7 ≤ k)
    (i : Nat) (hi : i + 1 < (phaseRows k).length)
    (htrans : LocalPhaseTransition k ((phaseRows k)[i]'(by omega))
      ((phaseRows k)[i + 1]'hi)) :
    match ((phaseRows k)[i]'(by omega)) with
    | .ordinary _ =>
        DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
            (fun c => .cell ⟨i + 1, by rw [phaseRows_length k hk] at hi; omega⟩ c)
            (fun c => .cell ⟨i + 1, by rw [phaseRows_length k hk] at hi; omega⟩ c) →
          DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
            (fun c => .cell ⟨i + 1, by rw [phaseRows_length k hk] at hi; omega⟩ c)
            (fun c => .cell ⟨i + 2, by rw [phaseRows_length k hk] at hi; omega⟩ c)
    | .seam _ =>
        DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
            (fun c => .cell ⟨i + 3, by rw [phaseRows_length k hk] at hi; omega⟩ c)
            (fun c => .cell ⟨i + 3, by rw [phaseRows_length k hk] at hi; omega⟩ c) →
          DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
            (fun c => .cell ⟨i + 3, by rw [phaseRows_length k hk] at hi; omega⟩ c)
            (fun c => .cell ⟨i + 2, by rw [phaseRows_length k hk] at hi; omega⟩ c) := by
  generalize htop : ((phaseRows k)[i]'(by omega)) = top at htrans ⊢
  generalize hbottom : ((phaseRows k)[i + 1]'hi) = bottom at htrans
  cases htrans with
  | ordinaryPred a ha0 ha =>
      simp only
      intro houter
      apply ordinary_top_transition_frontier k hk i hi _ ha _ htop hbottom _ houter
      intro q hq
      by_cases hqa : q < a
      · exact Or.inl ⟨by omega,
          (common_ordinary_ordinary_pred ha ha0 (by omega)).1 hqa⟩
      · exact Or.inr ⟨by omega,
          (common_ordinary_ordinary_pred ha ha0 (by omega)).2 (by omega)⟩
  | ordinarySucc a ha =>
      simp only
      intro houter
      apply ordinary_top_transition_frontier k hk i hi _ (by omega) _ htop hbottom _ houter
      intro q hq
      by_cases hqa : q ≤ a
      · exact Or.inl ⟨hqa,
          (common_ordinary_ordinary_succ ha (by omega)).1 hqa⟩
      · exact Or.inr ⟨by omega,
          (common_ordinary_ordinary_succ ha (by omega)).2 (by omega)⟩
  | ordinarySeamSame a ha =>
      simp only
      intro houter
      apply ordinary_top_transition_frontier k hk i hi _ ha _ htop hbottom _ houter
      intro q hq
      by_cases hqa : q < a
      · exact Or.inl ⟨by omega, common_ordinary_seam_same ha
          (seam_left_run ha (by omega) hqa).2⟩
      · exact Or.inr ⟨by omega, common_ordinary_seam_same ha
          (seam_right_run ha (by omega) (by omega)).1⟩
  | ordinarySeamSucc a ha =>
      simp only
      intro houter
      apply ordinary_top_transition_frontier k hk i hi _ (by omega) _ htop hbottom _ houter
      intro q hq
      by_cases hqa : q ≤ a
      · exact Or.inl ⟨hqa, common_ordinary_seam_succ ha
          (seam_left_run ha (by omega) (by omega)).2⟩
      · exact Or.inr ⟨by omega, common_ordinary_seam_succ ha
          (seam_right_run ha (by omega) (by omega)).1⟩
  | seamOrdinaryPred a ha0 ha =>
      simp only
      intro houter
      apply ordinary_bottom_transition_frontier k hk i hi _ (by omega) _ htop hbottom _ houter
      intro q hq
      by_cases hqa : q < a
      · exact Or.inl ⟨by omega, common_seam_ordinary_pred ha ha0
          (seam_left_run ha (by omega) hqa).2⟩
      · exact Or.inr ⟨by omega, common_seam_ordinary_pred ha ha0
          (seam_right_run ha (by omega) (by omega)).1⟩
  | seamOrdinarySame a ha =>
      simp only
      intro houter
      apply ordinary_bottom_transition_frontier k hk i hi _ ha _ htop hbottom _ houter
      intro q hq
      by_cases hqa : q < a
      · exact Or.inl ⟨by omega, common_seam_ordinary_same ha
          (seam_left_run ha (by omega) hqa).2⟩
      · exact Or.inr ⟨by omega, common_seam_ordinary_same ha
          (seam_right_run ha (by omega) (by omega)).1⟩

end GridGraphs
