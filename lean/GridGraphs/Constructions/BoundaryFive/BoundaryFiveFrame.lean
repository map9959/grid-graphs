import GridGraphs.Accounting.BoundaryFiveEquality

/-! # The concrete normalized boundary-five outer frame

Coordinates are zero-based. Only the outer boundary is preserved, except for
the five specified holes. The graph retains all grid vertices, including the
isolated next-ring vertex `(1,2)` and the isolated deep square.
-/

namespace GridGraphs.BoundaryFiveFrame

open SimpleGraph

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 200000

/-- The five canonical unpreserved boundary positions. -/
def BoundaryHole {n : Nat} (v : GridVertex n n) : Prop :=
  (v.1.val = 0 ∧ (v.2.val = 1 ∨ v.2.val = 2)) ∨
  (v.1.val = 1 ∧ v.2.val = n - 1) ∨
  (v.1.val = n - 1 ∧ v.2.val = n - 2) ∨
  (v.1.val = n - 2 ∧ v.2.val = 0)

/-- The boundary of the once-cropped square. -/
def NextRing {n : Nat} (v : GridVertex n n) : Prop :=
  1 ≤ v.1.val ∧ v.1.val ≤ n - 2 ∧
  1 ≤ v.2.val ∧ v.2.val ≤ n - 2 ∧
  (v.1.val = 1 ∨ v.1.val = n - 2 ∨ v.2.val = 1 ∨ v.2.val = n - 2)

def Fouter (n : Nat) : Set (GridVertex n n) :=
  {v | IsGridBoundary v ∧ ¬ BoundaryHole v}

def Houter (n : Nat) : SimpleGraph (GridVertex n n) :=
  forcedEdgeGraph (gridGraph n n) (Fouter n)

def w {n : Nat} (hn : 7 ≤ n) : GridVertex n n :=
  (⟨1, by omega⟩, ⟨2, by omega⟩)

theorem nextRing_not_boundary {n : Nat} {v : GridVertex n n}
    (hv : NextRing v) : ¬ IsGridBoundary v := by
  unfold NextRing at hv
  unfold IsGridBoundary
  omega

theorem nextRing_notMem_Fouter {n : Nat} {v : GridVertex n n}
    (hv : NextRing v) : v ∉ Fouter n :=
  fun h => nextRing_not_boundary hv h.1

/-- Actual coordinate classification of all forced spokes. At next-ring
corners, the excluded outer neighbor leaves precisely the listed side. -/
theorem spoke_iff {n : Nat} (hn : 7 ≤ n) {v p : GridVertex n n}
    (hv : NextRing v) :
    (Houter n).Adj v p ↔
      (v.1.val = 1 ∧ v.2.val ≠ 1 ∧ v.2.val ≠ 2 ∧
        p.1.val = 0 ∧ p.2.val = v.2.val) ∨
      (v.2.val = n - 2 ∧ v.1.val ≠ 1 ∧
        p.1.val = v.1.val ∧ p.2.val = n - 1) ∨
      (v.1.val = n - 2 ∧ v.2.val ≠ n - 2 ∧
        p.1.val = n - 1 ∧ p.2.val = v.2.val) ∨
      (v.2.val = 1 ∧ v.1.val ≠ n - 2 ∧
        p.1.val = v.1.val ∧ p.2.val = 0) := by
  have hnot := nextRing_notMem_Fouter hv
  change ((gridGraph n n).Adj v p ∧ (v ∈ Fouter n ∨ p ∈ Fouter n)) ↔ _
  simp only [hnot, false_or]
  simp only [gridGraph, adjacent, Fin.ext_iff, Fouter, Set.mem_ofPred_eq,
    IsGridBoundary, BoundaryHole]
  unfold NextRing at hv
  obtain ⟨hv1, hv2, hv3, hv4, _⟩ := hv
  have hr := p.1.isLt
  have hc := p.2.isLt
  constructor
  · rintro ⟨hadj, hb, hh⟩
    rcases hb with hb | hb | hb | hb
    · left
      refine ⟨?_, ?_, ?_, hb, ?_⟩ <;> omega
    · right; right; left
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · right; right; right
      refine ⟨?_, ?_, ?_, hb⟩ <;> omega
    · right; left
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · rintro (h | h | h | h) <;> refine ⟨?_, ?_, ?_⟩ <;> omega

theorem nextRing_adj_iff_preserved_neighbor {n : Nat} {v p : GridVertex n n}
    (hv : NextRing v) :
    (Houter n).Adj v p ↔ p ∈ Fouter n ∧ (gridGraph n n).Adj v p := by
  have hnot := nextRing_notMem_Fouter hv
  change (_ ∧ (v ∈ Fouter n ∨ p ∈ Fouter n)) ↔ _
  simp only [hnot, false_or, and_comm]

/-- Every next-ring vertex other than `(1,2)` has exactly one neighbor in
the full forced graph, and that neighbor is on the preserved boundary. -/
theorem nextRing_unique_neighbor {n : Nat} (hn : 7 ≤ n)
    (v : GridVertex n n) (hv : NextRing v) (hne : v ≠ w hn) :
    ∃! p, (Houter n).Adj v p := by
  have hw : ¬ (v.1.val = 1 ∧ v.2.val = 2) := by
    intro h
    apply hne
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  have unique : ∀ p q, (Houter n).Adj v p → (Houter n).Adj v q → p = q := by
    intro p q hp hq
    rw [spoke_iff hn hv] at hp hq
    apply Prod.ext <;> apply Fin.ext <;> unfold NextRing at hv <;> omega
  suffices hex : ∃ p, (Houter n).Adj v p by
    obtain ⟨p, hp⟩ := hex
    exact ⟨p, hp, fun q hq => unique q p hq hp⟩
  by_cases ht : v.1.val = 1 ∧ v.2.val ≠ 1 ∧ v.2.val ≠ 2
  · refine ⟨(⟨0, by omega⟩, v.2), (spoke_iff hn hv).mpr ?_⟩
    exact Or.inl ⟨ht.1, ht.2.1, ht.2.2, rfl, rfl⟩
  by_cases hr : v.2.val = n - 2 ∧ v.1.val ≠ 1
  · refine ⟨(v.1, ⟨n - 1, by omega⟩), (spoke_iff hn hv).mpr ?_⟩
    exact Or.inr (Or.inl ⟨hr.1, hr.2, rfl, rfl⟩)
  by_cases hb : v.1.val = n - 2 ∧ v.2.val ≠ n - 2
  · refine ⟨(⟨n - 1, by omega⟩, v.2), (spoke_iff hn hv).mpr ?_⟩
    exact Or.inr (Or.inr (Or.inl ⟨hb.1, hb.2, rfl, rfl⟩))
  refine ⟨(v.1, ⟨0, by omega⟩), (spoke_iff hn hv).mpr ?_⟩
  right; right; right
  unfold NextRing at hv
  exact ⟨by omega, by omega, rfl, rfl⟩

theorem nextRing_unique_Fouter_neighbor {n : Nat} (hn : 7 ≤ n)
    (v : GridVertex n n) (hv : NextRing v) (hne : v ≠ w hn) :
    ∃! p, p ∈ Fouter n ∧ IsGridBoundary p ∧ (gridGraph n n).Adj v p := by
  obtain ⟨p, hp, hu⟩ := nextRing_unique_neighbor hn v hv hne
  have hp' := (nextRing_adj_iff_preserved_neighbor hv).mp hp
  refine ⟨p, ⟨hp'.1, hp'.1.1, hp'.2⟩, ?_⟩
  intro q hq
  exact hu q ((nextRing_adj_iff_preserved_neighbor hv).mpr ⟨hq.1, hq.2.2⟩)

theorem w_nextRing {n : Nat} (hn : 7 ≤ n) : NextRing (w hn) := by
  dsimp [NextRing, w]
  omega

theorem w_no_neighbor {n : Nat} (hn : 7 ≤ n) (p : GridVertex n n) :
    ¬ (Houter n).Adj (w hn) p := by
  rw [spoke_iff hn (w_nextRing hn)]
  dsimp [w]
  omega

theorem w_no_Fouter_neighbor {n : Nat} (hn : 7 ≤ n) (p : GridVertex n n) :
    ¬ (p ∈ Fouter n ∧ (gridGraph n n).Adj (w hn) p) := by
  rw [← nextRing_adj_iff_preserved_neighbor (w_nextRing hn)]
  exact w_no_neighbor hn p

/-- Any forced edge stays in the outer two rings. -/
theorem adj_outer_two_rings {n : Nat} (hn : 7 ≤ n) {v p : GridVertex n n}
    (h : (Houter n).Adj v p) : IsGridBoundary v ∨ NextRing v := by
  rcases h with ⟨hadj, hv | hp⟩
  · exact Or.inl hv.1
  · have hb := hp.1
    simp only [gridGraph, adjacent, Fin.ext_iff] at hadj
    unfold IsGridBoundary at hb ⊢
    unfold NextRing
    have hr := v.1.isLt
    have hc := v.2.isLt
    omega

theorem boundary_mem_support {n : Nat} (hn : 7 ≤ n)
    (v : GridVertex n n) (hv : IsGridBoundary v) : v ∈ (Houter n).support := by
  rw [SimpleGraph.mem_support]
  by_cases hF : v ∈ Fouter n
  · by_cases hzero : v.1.val = 0
    · refine ⟨(⟨1, by omega⟩, v.2), ?_⟩
      exact ⟨by simp [gridGraph, adjacent, Fin.ext_iff, hzero], Or.inl hF⟩
    · refine ⟨(⟨v.1.val - 1, by have := v.1.isLt; omega⟩, v.2), ?_⟩
      refine ⟨?_, Or.inl hF⟩
      simp [gridGraph, adjacent, Fin.ext_iff]
      omega
  have hhole : BoundaryHole v := by
    by_contra hh
    exact hF ⟨hv, hh⟩
  unfold BoundaryHole at hhole
  rcases hhole with ⟨hrow, hcol | hcol⟩ | ⟨hrow, hcol⟩ |
    ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
  · refine ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), ?_⟩
    simp [Houter, forcedEdgeGraph, gridGraph, adjacent, Fouter,
      IsGridBoundary, BoundaryHole, Fin.ext_iff, hrow, hcol]
    omega
  · refine ⟨(⟨0, by omega⟩, ⟨3, by omega⟩), ?_⟩
    simp [Houter, forcedEdgeGraph, gridGraph, adjacent, Fouter,
      IsGridBoundary, BoundaryHole, Fin.ext_iff, hrow, hcol]
    omega
  · refine ⟨(⟨0, by omega⟩, ⟨n - 1, by omega⟩), ?_⟩
    simp [Houter, forcedEdgeGraph, gridGraph, adjacent, Fouter,
      IsGridBoundary, BoundaryHole, Fin.ext_iff, hrow, hcol]
    omega
  · refine ⟨(⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩), ?_⟩
    simp [Houter, forcedEdgeGraph, gridGraph, adjacent, Fouter,
      IsGridBoundary, BoundaryHole, Fin.ext_iff, hrow, hcol]
    omega
  · refine ⟨(⟨n - 1, by omega⟩, ⟨0, by omega⟩), ?_⟩
    simp [Houter, forcedEdgeGraph, gridGraph, adjacent, Fouter,
      IsGridBoundary, BoundaryHole, Fin.ext_iff, hrow, hcol]
    omega

/-- Exact support on the full vertex type: the two outer rings minus `w`. -/
theorem mem_support_iff {n : Nat} (hn : 7 ≤ n) (v : GridVertex n n) :
    v ∈ (Houter n).support ↔
      (IsGridBoundary v ∨ NextRing v) ∧ v ≠ w hn := by
  constructor
  · intro hv
    obtain ⟨p, hp⟩ := (SimpleGraph.mem_support _).mp hv
    refine ⟨adj_outer_two_rings hn hp, ?_⟩
    intro heq
    subst v
    exact w_no_neighbor hn p hp
  · rintro ⟨hb | hr, hne⟩
    · exact boundary_mem_support hn v hb
    · obtain ⟨p, hp, _⟩ := nextRing_unique_neighbor hn v hr hne
      exact (SimpleGraph.mem_support _).mpr ⟨p, hp⟩

theorem support_eq {n : Nat} (hn : 7 ≤ n) :
    (Houter n).support =
      {v | (IsGridBoundary v ∨ NextRing v) ∧ v ≠ w hn} := by
  ext v
  exact mem_support_iff hn v

theorem deep_not_mem_support {n : Nat} (hn : 7 ≤ n) (v : GridVertex n n)
    (hrlo : 2 ≤ v.1.val) (hrhi : v.1.val ≤ n - 3)
    (hclo : 2 ≤ v.2.val) (hchi : v.2.val ≤ n - 3) :
    v ∉ (Houter n).support := by
  rw [mem_support_iff hn]
  unfold IsGridBoundary NextRing
  omega

/-- Clockwise path rank, starting at `(0,2)` and ending at `(0,1)`.
The only cut is the unforced edge between these two vertices. -/
def boundaryRank {n : Nat} (v : GridVertex n n) : Nat :=
  if v.1.val = 0 then
    if 2 ≤ v.2.val then v.2.val - 2 else 4 * n - 6 + v.2.val
  else if v.2.val + 1 = n then n + v.1.val - 3
  else if v.1.val + 1 = n then 3 * n - 5 - v.2.val
  else 4 * n - 6 - v.1.val

theorem boundaryRank_lt {n : Nat} (hn : 7 ≤ n) (v : GridVertex n n)
    (_hv : IsGridBoundary v) : boundaryRank v < 4 * n - 4 := by
  have hr := v.1.isLt
  have hc := v.2.isLt
  unfold boundaryRank
  unfold IsGridBoundary at _hv
  split_ifs <;> omega

theorem boundaryRank_injective {n : Nat} (hn : 7 ≤ n)
    {v p : GridVertex n n} (hv : IsGridBoundary v) (hp : IsGridBoundary p)
    (he : boundaryRank v = boundaryRank p) : v = p := by
  have hr := v.1.isLt
  have hc := v.2.isLt
  have pr := p.1.isLt
  have pc := p.2.isLt
  unfold IsGridBoundary at hv hp
  unfold boundaryRank at he
  split_ifs at he <;> apply Prod.ext <;> apply Fin.ext <;> omega

private theorem hole_rank {n : Nat} (hn : 7 ≤ n) {v : GridVertex n n}
    (hv : BoundaryHole v) :
    boundaryRank v = 0 ∨ boundaryRank v = 4 * n - 5 ∨
    boundaryRank v = n - 2 ∨ boundaryRank v = 2 * n - 3 ∨
    boundaryRank v = 3 * n - 4 := by
  unfold BoundaryHole at hv
  rcases hv with ⟨hr, hc | hc⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩ | ⟨hr, hc⟩ <;>
    simp [boundaryRank, hr, hc] <;> (try split_ifs) <;> omega

set_option maxHeartbeats 400000 in
/-- On the boundary, the concrete forced graph is exactly a linear path in
`boundaryRank` order, not a cycle. -/
theorem boundary_adj_iff_rank {n : Nat} (hn : 7 ≤ n)
    {v p : GridVertex n n} (hv : IsGridBoundary v) (hp : IsGridBoundary p) :
    (Houter n).Adj v p ↔
      boundaryRank v + 1 = boundaryRank p ∨ boundaryRank p + 1 = boundaryRank v := by
  have hr := v.1.isLt
  have hc := v.2.isLt
  have pr := p.1.isLt
  have pc := p.2.isLt
  change ((gridGraph n n).Adj v p ∧ (v ∈ Fouter n ∨ p ∈ Fouter n)) ↔ _
  simp only [Fouter, Set.mem_ofPred_eq, hv, hp, true_and,
    gridGraph, adjacent, Fin.ext_iff]
  unfold IsGridBoundary at hv hp
  constructor
  · rintro ⟨ha, hf⟩
    have hgap : ¬ (v.1.val = 0 ∧ p.1.val = 0 ∧
        ((v.2.val = 1 ∧ p.2.val = 2) ∨ (v.2.val = 2 ∧ p.2.val = 1))) := by
      unfold BoundaryHole at hf
      omega
    clear hf
    unfold boundaryRank
    split_ifs <;> omega
  · intro h
    have ha : (v.1.val = p.1.val ∧
        (v.2.val + 1 = p.2.val ∨ p.2.val + 1 = v.2.val)) ∨
        (v.2.val = p.2.val ∧
        (v.1.val + 1 = p.1.val ∨ p.1.val + 1 = v.1.val)) := by
      unfold boundaryRank at h
      split_ifs at h <;> omega
    refine ⟨ha, ?_⟩
    by_contra hf
    have hh : BoundaryHole v ∧ BoundaryHole p := by
      exact ⟨by by_contra h; exact hf (Or.inl h),
        by by_contra h; exact hf (Or.inr h)⟩
    have hvr := hole_rank hn hh.1
    have hpr := hole_rank hn hh.2
    omega

/-- Every path rank is realized by an explicit boundary coordinate. -/
theorem exists_boundaryRank {n : Nat} (hn : 7 ≤ n) (k : Nat) (hk : k < 4 * n - 4) :
    ∃ v : GridVertex n n, IsGridBoundary v ∧ boundaryRank v = k := by
  by_cases ht : k < n - 2
  · refine ⟨(⟨0, by omega⟩, ⟨k + 2, by omega⟩), ?_⟩
    simp [IsGridBoundary, boundaryRank]
  by_cases hr : k < 2 * n - 3
  · refine ⟨(⟨k + 3 - n, by omega⟩, ⟨n - 1, by omega⟩), ?_⟩
    dsimp [IsGridBoundary, boundaryRank]
    split_ifs <;> omega
  by_cases hb : k < 3 * n - 4
  · refine ⟨(⟨n - 1, by omega⟩, ⟨3 * n - 5 - k, by omega⟩), ?_⟩
    dsimp [IsGridBoundary, boundaryRank]
    split_ifs <;> omega
  by_cases hl : k < 4 * n - 6
  · refine ⟨(⟨4 * n - 6 - k, by omega⟩, ⟨0, by omega⟩), ?_⟩
    dsimp [IsGridBoundary, boundaryRank]
    split_ifs <;> omega
  · refine ⟨(⟨0, by omega⟩, ⟨k - (4 * n - 6), by omega⟩), ?_⟩
    dsimp [IsGridBoundary, boundaryRank]
    split_ifs <;> omega

/-- The canonical outer frame is a forest, without any feasibility hypothesis.
A cycle cannot visit a spoke leaf. On the perimeter its maximum-rank vertex
would have two distinct predecessors of the same rank. -/
theorem Houter_isAcyclic {n : Nat} (hn : 7 ≤ n) : (Houter n).IsAcyclic := by
  classical
  intro a c hc
  have onBoundary (x : GridVertex n n) (hx : x ∈ c.support) : IsGridBoundary x := by
    let d := c.rotate x hx
    have hd : d.IsCycle := hc.rotate hx
    have hs := d.adj_snd hd.not_nil
    have ht := (d.adj_penultimate hd.not_nil).symm
    have hxS : x ∈ (Houter n).support := (SimpleGraph.mem_support _).mpr ⟨d.snd, hs⟩
    rcases (mem_support_iff hn x).mp hxS with ⟨hb | hr, hne⟩
    · exact hb
    · obtain ⟨p, _, hu⟩ := nextRing_unique_neighbor hn x hr hne
      exact False.elim (hd.snd_ne_penultimate ((hu _ hs).trans (hu _ ht).symm))
  obtain ⟨x, hx, hmax⟩ := c.support.toFinset.exists_max_image boundaryRank
    ⟨a, List.mem_toFinset.mpr c.start_mem_support⟩
  have hx' : x ∈ c.support := List.mem_toFinset.mp hx
  let d := c.rotate x hx'
  have hd : d.IsCycle := hc.rotate hx'
  have hs : d.snd ∈ c.support := by
    exact (c.mem_support_rotate_iff x hx').mp (d.getVert_mem_support 1)
  have ht : d.penultimate ∈ c.support := by
    exact (c.mem_support_rotate_iff x hx').mp (d.getVert_mem_support (d.length - 1))
  have hsr := (boundary_adj_iff_rank hn (onBoundary x hx') (onBoundary _ hs)).mp
    (d.adj_snd hd.not_nil)
  have htr := (boundary_adj_iff_rank hn (onBoundary x hx') (onBoundary _ ht)).mp
    (d.adj_penultimate hd.not_nil).symm
  have hsm := hmax _ (List.mem_toFinset.mpr hs)
  have htm := hmax _ (List.mem_toFinset.mpr ht)
  exact hd.snd_ne_penultimate
    (boundaryRank_injective hn (onBoundary _ hs) (onBoundary _ ht) (by omega))

/-- The nonisolated part of the canonical outer frame is one tree. The
perimeter path is connected in rank order and every other support vertex
attaches to it by its unique spoke. -/
theorem support_isTree {n : Nat} (hn : 7 ≤ n) :
    ((Houter n).induce (Houter n).support).IsTree := by
  classical
  let z : GridVertex n n := (⟨0, by omega⟩, ⟨2, by omega⟩)
  have hz : IsGridBoundary z := Or.inl rfl
  have hzrank : boundaryRank z = 0 := by simp [boundaryRank, z]
  let root : (Houter n).support := ⟨z, boundary_mem_support hn z hz⟩
  let S := (Houter n).induce (Houter n).support
  have boundaryReach : ∀ k, ∀ (v : GridVertex n n) (hv : IsGridBoundary v),
      boundaryRank v = k → S.Reachable root ⟨v, boundary_mem_support hn v hv⟩ := by
    intro k
    induction k with
    | zero =>
      intro v hv hk
      have he : v = z := boundaryRank_injective hn hv hz (hk.trans hzrank.symm)
      have he' : (⟨v, boundary_mem_support hn v hv⟩ : (Houter n).support) = root :=
        Subtype.ext he
      rw [he']
    | succ k ih =>
      intro v hv hk
      have hbound := boundaryRank_lt hn v hv
      obtain ⟨p, hp, hpk⟩ := exists_boundaryRank hn k (by omega)
      have hadj : S.Adj ⟨p, boundary_mem_support hn p hp⟩
          ⟨v, boundary_mem_support hn v hv⟩ :=
        (boundary_adj_iff_rank hn hp hv).mpr (Or.inl (by omega))
      exact (ih p hp hpk).trans hadj.reachable
  have reach (v : (Houter n).support) : S.Reachable root v := by
    rcases (mem_support_iff hn v.val).mp v.property with ⟨hb | hr, hne⟩
    · exact boundaryReach _ v.val hb rfl
    · obtain ⟨p, hp, _⟩ := nextRing_unique_Fouter_neighbor hn v.val hr hne
      have hadj : S.Adj ⟨p, boundary_mem_support hn p hp.2.1⟩ v :=
        ((nextRing_adj_iff_preserved_neighbor hr).mpr ⟨hp.1, hp.2.2⟩).symm
      exact (boundaryReach _ p hp.2.1 rfl).trans hadj.reachable
  let : Nonempty (Houter n).support := ⟨root⟩
  exact ⟨SimpleGraph.Connected.mk (fun a b => (reach a).symm.trans (reach b)),
    (Houter_isAcyclic hn).induce _⟩

end GridGraphs.BoundaryFiveFrame
