import GridGraphs.GridBoundaryCycle
import GridGraphs.GridCropComponents
import GridGraphs.GridDual

/-!
# Closing a grid crosscut in a one-cell collar

This file contains only combinatorial graph theory.  A path in an `m x n` grid
is translated into the central rectangle of the `(m + 2) x (n + 2)` grid.  A
chosen simple arc of the outer boundary, together with its two radial edges,
closes the translated path to a cycle.  No Jordan or crossing theorem is used.
-/

namespace GridGraphs

open SimpleGraph

/-! ## Finite clockwise arcs in the boundary numbering -/

private theorem cyclicOffset_succ {k : Nat} (hk : 0 < k) (i : Fin k) (d : Nat) :
    cyclicOffset hk (cyclicOffset hk i 1) d = cyclicOffset hk i (d + 1) := by
  apply Fin.ext
  simp only [cyclicOffset]
  rw [Nat.add_mod]
  rw [Nat.mod_mod, ← Nat.add_mod]
  congr 1
  omega

private theorem gridBoundarySucc_eq_cyclicOffset {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    gridBoundarySucc hm hn i =
      cyclicOffset (gridBoundaryLength_pos hm hn) i 1 := by
  rfl

/-- Walk clockwise for exactly `d` boundary edges. -/
def gridBoundaryForwardWalk {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : (d : Nat) →
    (gridGraph m n).Walk (gridBoundaryVertex hm hn i)
      (gridBoundaryVertex hm hn
        (cyclicOffset (gridBoundaryLength_pos hm hn) i d))
  | 0 => Walk.nil.copy rfl (congrArg (gridBoundaryVertex hm hn) (by
      apply Fin.ext
      simp [cyclicOffset, Nat.mod_eq_of_lt i.isLt]))
  | d + 1 =>
      (Walk.cons (gridBoundaryVertex_succ_adj hm hn i)
        (gridBoundaryForwardWalk hm hn (gridBoundarySucc hm hn i) d)).copy rfl
          (congrArg (gridBoundaryVertex hm hn)
            (cyclicOffset_succ (gridBoundaryLength_pos hm hn) i d))

@[simp] theorem length_gridBoundaryForwardWalk {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) (d : Nat) :
    (gridBoundaryForwardWalk hm hn i d).length = d := by
  induction d generalizing i with
  | zero => simp [gridBoundaryForwardWalk]
  | succ d ih => simp [gridBoundaryForwardWalk, ih]

@[simp] theorem support_gridBoundaryForwardWalk {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) (d : Nat) :
    (gridBoundaryForwardWalk hm hn i d).support =
      (List.range (d + 1)).map fun t =>
        gridBoundaryVertex hm hn
          (cyclicOffset (gridBoundaryLength_pos hm hn) i t) := by
  induction d generalizing i with
  | zero =>
      simp [gridBoundaryForwardWalk, cyclicOffset, Nat.mod_eq_of_lt i.isLt]
  | succ d ih =>
      simp only [gridBoundaryForwardWalk, Walk.support_copy, Walk.support_cons, ih]
      conv_rhs =>
        rw [show d + 1 + 1 = (d + 1) + 1 by omega, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      congr 1
      · congr 1
        apply Fin.ext
        simp [cyclicOffset, Nat.mod_eq_of_lt i.isLt]
      · apply List.map_congr_left
        intro t ht
        rw [List.mem_range] at ht
        congr 1
        rw [gridBoundarySucc_eq_cyclicOffset, cyclicOffset_succ]

private theorem cyclicOffset_injective_below {k : Nat} (hk : 0 < k) (i : Fin k)
    {s t : Nat} (hs : s < k) (ht : t < k)
    (h : cyclicOffset hk i s = cyclicOffset hk i t) : s = t := by
  have hs' : cyclicOffset hk i s = i + ⟨s, hs⟩ := by
    apply Fin.ext
    simp [cyclicOffset, Fin.add_def]
  have ht' : cyclicOffset hk i t = i + ⟨t, ht⟩ := by
    apply Fin.ext
    simp [cyclicOffset, Fin.add_def]
  rw [hs', ht'] at h
  have hfin : (⟨s, hs⟩ : Fin k) = ⟨t, ht⟩ := add_left_cancel h
  exact congrArg Fin.val hfin

/-- A clockwise boundary segment shorter than the perimeter is simple. -/
theorem gridBoundaryForwardWalk_isPath {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) {d : Nat}
    (hd : d < gridBoundaryLength m n) :
    (gridBoundaryForwardWalk hm hn i d).IsPath := by
  rw [Walk.isPath_def, support_gridBoundaryForwardWalk]
  apply List.Nodup.map_on
  intro s hs t ht hst
  apply cyclicOffset_injective_below (gridBoundaryLength_pos hm hn) i
  · rw [List.mem_range] at hs
    omega
  · rw [List.mem_range] at ht
    omega
  · exact gridBoundaryVertex_injective hm hn hst
  · exact List.nodup_range

/-- Membership in a finite clockwise arc is membership in its cyclic interval. -/
theorem mem_support_gridBoundaryForwardWalk_iff {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) (d : Nat)
    (x : GridVertex m n) :
    x ∈ (gridBoundaryForwardWalk hm hn i d).support ↔
      ∃ t ≤ d, x = gridBoundaryVertex hm hn
        (cyclicOffset (gridBoundaryLength_pos hm hn) i t) := by
  rw [support_gridBoundaryForwardWalk, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_range] at ht
    exact ⟨t, by omega, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ?_, rfl⟩
    rw [List.mem_range]
    omega

/-- Translation of a grid into the central rectangle of its one-cell collar. -/
def gridCollarEmbedding (m n : Nat) : GridVertex m n ↪ GridVertex (m + 2) (n + 2) :=
  gridOffsetEmbedding 1 1 (by omega) (by omega)

/-- The collar translation as an induced graph embedding. -/
def gridCollarGraphEmbedding (m n : Nat) :
    gridGraph m n ↪g gridGraph (m + 2) (n + 2) :=
  gridOffsetGraphEmbedding 1 1 (by omega) (by omega)

@[simp] theorem gridCollarEmbedding_fst_val {m n : Nat} (v : GridVertex m n) :
    (gridCollarEmbedding m n v).1.val = v.1.val + 1 := by
  simp [gridCollarEmbedding, Nat.add_comm]

@[simp] theorem gridCollarEmbedding_snd_val {m n : Nat} (v : GridVertex m n) :
    (gridCollarEmbedding m n v).2.val = v.2.val + 1 := by
  simp [gridCollarEmbedding, Nat.add_comm]

/-- Translated vertices never lie on the outer frame. -/
theorem gridCollarEmbedding_not_boundary {m n : Nat} (v : GridVertex m n) :
    ¬IsGridBoundary (gridCollarEmbedding m n v) := by
  simp only [IsGridBoundary, gridCollarEmbedding_fst_val,
    gridCollarEmbedding_snd_val]
  omega

/-- The central rectangle and the outer frame are disjoint. -/
theorem gridCollarEmbedding_ne_of_boundary {m n : Nat} (v : GridVertex m n)
    {x : GridVertex (m + 2) (n + 2)} (hx : IsGridBoundary x) :
    gridCollarEmbedding m n v ≠ x := by
  rintro rfl
  exact gridCollarEmbedding_not_boundary v hx

/-! ## Canonical collar ports -/

/-- Outer-frame port on the side followed by the clockwise boundary edge out
of `i`.  At a corner this selects the outgoing side. -/
def clockwiseOutPort {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridVertex (m + 2) (n + 2) :=
  if htop : i.val < n - 1 then
    (⟨0, by omega⟩, ⟨i.val + 1, by omega⟩)
  else if hright : i.val < n + m - 2 then
    (⟨i.val + 1 - n + 1, by omega⟩, ⟨n + 1, by omega⟩)
  else if hbottom : i.val < m + 2 * n - 3 then
    (⟨m + 1, by omega⟩, ⟨m + 2 * n - 2 - i.val, by omega⟩)
  else
    (⟨gridBoundaryLength m n - i.val + 1, by
      unfold gridBoundaryLength at *
      omega⟩, ⟨0, by omega⟩)

/-- Outer-frame port on the side preceding `i` in clockwise order.  At a
corner this selects the incoming side. -/
def clockwiseInPort {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridVertex (m + 2) (n + 2) :=
  if hzero : i.val = 0 then
    (⟨1, by omega⟩, ⟨0, by omega⟩)
  else if htop : i.val < n then
    (⟨0, by omega⟩, ⟨i.val + 1, by omega⟩)
  else if hright : i.val < n + m - 1 then
    (⟨i.val - n + 2, by omega⟩, ⟨n + 1, by omega⟩)
  else if hbottom : i.val < m + 2 * n - 2 then
    (⟨m + 1, by omega⟩, ⟨m + 2 * n - 2 - i.val, by omega⟩)
  else
    (⟨gridBoundaryLength m n - i.val + 1, by
      unfold gridBoundaryLength at *
      omega⟩, ⟨0, by omega⟩)

theorem clockwiseOutPort_boundary {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : IsGridBoundary (clockwiseOutPort hm hn i) := by
  unfold clockwiseOutPort IsGridBoundary
  split_ifs <;> simp_all

theorem clockwiseInPort_boundary {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : IsGridBoundary (clockwiseInPort hm hn i) := by
  unfold clockwiseInPort IsGridBoundary
  split_ifs <;> simp_all

theorem clockwiseOutPort_spoke {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) :
    (gridGraph (m + 2) (n + 2)).Adj
      (gridCollarEmbedding m n (gridBoundaryVertex hm hn i))
      (clockwiseOutPort hm hn i) := by
  unfold clockwiseOutPort gridBoundaryVertex gridGraph adjacent
  split_ifs <;> simp_all [gridCollarEmbedding, gridOffsetEmbedding] <;>
    unfold gridBoundaryLength at * <;> try omega

theorem clockwiseInPort_spoke {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) :
    (gridGraph (m + 2) (n + 2)).Adj
      (gridCollarEmbedding m n (gridBoundaryVertex hm hn i))
      (clockwiseInPort hm hn i) := by
  unfold clockwiseInPort gridBoundaryVertex gridGraph adjacent
  split_ifs <;> simp_all [gridCollarEmbedding, gridOffsetEmbedding] <;>
    unfold gridBoundaryLength at * <;> omega

/-- Canonical boundary position of a known outer-frame vertex. -/
noncomputable def collarBoundaryPosition {m n : Nat}
    (x : GridVertex (m + 2) (n + 2)) (hx : IsGridBoundary x) :
    GridBoundaryPosition (m + 2) (n + 2) :=
  (gridBoundaryEquiv (by omega) (by omega)).symm ⟨x, hx⟩

@[simp] theorem gridBoundaryVertex_collarBoundaryPosition {m n : Nat}
    (x : GridVertex (m + 2) (n + 2)) (hx : IsGridBoundary x) :
    gridBoundaryVertex (by omega) (by omega) (collarBoundaryPosition x hx) = x := by
  exact congrArg Subtype.val
    ((gridBoundaryEquiv (by omega) (by omega)).apply_symm_apply ⟨x, hx⟩)

/-- Clockwise distance in a nonempty finite cyclic numbering. -/
def cyclicForwardDistance {k : Nat} (_hk : 0 < k) (i j : Fin k) : Nat :=
  if i.val ≤ j.val then j.val - i.val else j.val + k - i.val

theorem cyclicForwardDistance_lt {k : Nat} (hk : 0 < k) (i j : Fin k) :
    cyclicForwardDistance hk i j < k := by
  unfold cyclicForwardDistance
  split_ifs <;> omega

theorem cyclicOffset_forwardDistance {k : Nat} (hk : 0 < k) (i j : Fin k) :
    cyclicOffset hk i (cyclicForwardDistance hk i j) = j := by
  apply Fin.ext
  change (i.val + cyclicForwardDistance hk i j) % k = j.val
  unfold cyclicForwardDistance
  split_ifs with h
  · rw [Nat.add_sub_of_le h, Nat.mod_eq_of_lt j.isLt]
  · have hij : i.val ≤ j.val + k := by omega
    rw [Nat.add_sub_of_le hij]
    simp [Nat.mod_eq_of_lt j.isLt]

noncomputable def clockwiseOutPortPosition {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridBoundaryPosition (m + 2) (n + 2) :=
  collarBoundaryPosition (clockwiseOutPort hm hn i) (clockwiseOutPort_boundary hm hn i)

noncomputable def clockwiseInPortPosition {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridBoundaryPosition (m + 2) (n + 2) :=
  collarBoundaryPosition (clockwiseInPort hm hn i) (clockwiseInPort_boundary hm hn i)

@[simp] theorem boundaryVertex_clockwiseOutPortPosition {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    gridBoundaryVertex (by omega) (by omega) (clockwiseOutPortPosition hm hn i) =
      clockwiseOutPort hm hn i := by
  apply gridBoundaryVertex_collarBoundaryPosition

@[simp] theorem boundaryVertex_clockwiseInPortPosition {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i : GridBoundaryPosition m n) :
    gridBoundaryVertex (by omega) (by omega) (clockwiseInPortPosition hm hn i) =
      clockwiseInPort hm hn i := by
  apply gridBoundaryVertex_collarBoundaryPosition

/-- The canonical clockwise outer-frame arc corresponding to the cyclic
boundary interval from `i` to `j`. -/
noncomputable def clockwiseOuterArc {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    (gridGraph (m + 2) (n + 2)).Walk
      (clockwiseOutPort hm hn i) (clockwiseInPort hm hn j) :=
  let hk := gridBoundaryLength_pos (show 2 ≤ m + 2 by omega) (show 2 ≤ n + 2 by omega)
  let s := clockwiseOutPortPosition hm hn i
  let e := clockwiseInPortPosition hm hn j
  (gridBoundaryForwardWalk (by omega) (by omega) s
    (cyclicForwardDistance hk s e)).copy
      (boundaryVertex_clockwiseOutPortPosition hm hn i) (by
        rw [cyclicOffset_forwardDistance]
        exact boundaryVertex_clockwiseInPortPosition hm hn j)

/-- The counterclockwise outer-frame arc, defined as the reverse of the
clockwise complementary interval. -/
noncomputable def counterclockwiseOuterArc {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    (gridGraph (m + 2) (n + 2)).Walk
      (clockwiseInPort hm hn i) (clockwiseOutPort hm hn j) :=
  (clockwiseOuterArc hm hn j i).reverse

theorem clockwiseOuterArc_isPath {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) : (clockwiseOuterArc hm hn i j).IsPath := by
  unfold clockwiseOuterArc
  rw [Walk.isPath_copy]
  apply gridBoundaryForwardWalk_isPath
  apply cyclicForwardDistance_lt

theorem counterclockwiseOuterArc_isPath {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    (counterclockwiseOuterArc hm hn i j).IsPath :=
  (clockwiseOuterArc_isPath hm hn j i).reverse

theorem clockwiseOuterArc_on_boundary {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) {x : GridVertex (m + 2) (n + 2)}
    (hx : x ∈ (clockwiseOuterArc hm hn i j).support) : IsGridBoundary x := by
  unfold clockwiseOuterArc at hx
  rw [Walk.support_copy, mem_support_gridBoundaryForwardWalk_iff] at hx
  obtain ⟨t, -, rfl⟩ := hx
  apply gridBoundaryVertex_isBoundary

theorem counterclockwiseOuterArc_on_boundary {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    {x : GridVertex (m + 2) (n + 2)}
    (hx : x ∈ (counterclockwiseOuterArc hm hn i j).support) : IsGridBoundary x := by
  unfold counterclockwiseOuterArc at hx
  rw [Walk.support_reverse, List.mem_reverse] at hx
  exact clockwiseOuterArc_on_boundary hm hn j i hx

/-- A selected perimeter arc in the collar.  At a corner, `startPort` and
`endPort` record which of the two outward radial edges was selected. -/
structure GridCollarArc {m n : Nat} (a b : GridVertex m n) where
  startPort : GridVertex (m + 2) (n + 2)
  endPort : GridVertex (m + 2) (n + 2)
  arc : (gridGraph (m + 2) (n + 2)).Walk startPort endPort
  start_spoke : (gridGraph (m + 2) (n + 2)).Adj
    (gridCollarEmbedding m n a) startPort
  end_spoke : (gridGraph (m + 2) (n + 2)).Adj
    (gridCollarEmbedding m n b) endPort
  arc_isPath : arc.IsPath
  arc_on_outer_frame : ∀ x ∈ arc.support, IsGridBoundary x

namespace GridCollarArc

variable {m n : Nat} {a b : GridVertex m n}

/-- Canonical collar arc following the clockwise cyclic boundary interval. -/
noncomputable def clockwise {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    GridCollarArc (gridBoundaryVertex hm hn i) (gridBoundaryVertex hm hn j) where
  startPort := clockwiseOutPort hm hn i
  endPort := clockwiseInPort hm hn j
  arc := clockwiseOuterArc hm hn i j
  start_spoke := clockwiseOutPort_spoke hm hn i
  end_spoke := clockwiseInPort_spoke hm hn j
  arc_isPath := clockwiseOuterArc_isPath hm hn i j
  arc_on_outer_frame := fun _ hx => clockwiseOuterArc_on_boundary hm hn i j hx

/-- Canonical collar arc following the counterclockwise cyclic boundary
interval. -/
noncomputable def counterclockwise {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) :
    GridCollarArc (gridBoundaryVertex hm hn i) (gridBoundaryVertex hm hn j) where
  startPort := clockwiseInPort hm hn i
  endPort := clockwiseOutPort hm hn j
  arc := counterclockwiseOuterArc hm hn i j
  start_spoke := clockwiseInPort_spoke hm hn i
  end_spoke := clockwiseOutPort_spoke hm hn j
  arc_isPath := counterclockwiseOuterArc_isPath hm hn i j
  arc_on_outer_frame := fun _ hx => counterclockwiseOuterArc_on_boundary hm hn i j hx

/-- Either canonical cyclic interval between two boundary positions. -/
inductive CanonicalChoice where
  | clockwise
  | counterclockwise
  deriving DecidableEq

/-- Select one of the two canonical outer-frame intervals. -/
noncomputable def canonical (choice : CanonicalChoice) {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n) :
    GridCollarArc (gridBoundaryVertex hm hn i) (gridBoundaryVertex hm hn j) :=
  match choice with
  | .clockwise => clockwise hm hn i j
  | .counterclockwise => counterclockwise hm hn i j

/-- No vertex of the outer arc belongs to the embedded original grid. -/
theorem embedded_not_mem_arc (A : GridCollarArc a b) (v : GridVertex m n) :
    gridCollarEmbedding m n v ∉ A.arc.support := by
  intro hv
  exact gridCollarEmbedding_not_boundary v (A.arc_on_outer_frame _ hv)

/-- Exact cyclic-interval support of the canonical clockwise arc. -/
theorem mem_clockwise_arc_iff {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (clockwise hm hn i j).arc.support ↔
      ∃ t ≤ cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn i) (clockwiseInPortPosition hm hn j),
        x = gridBoundaryVertex (by omega) (by omega)
          (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
            (clockwiseOutPortPosition hm hn i) t) := by
  unfold clockwise clockwiseOuterArc
  rw [Walk.support_copy, mem_support_gridBoundaryForwardWalk_iff]

/-- Counterclockwise support is the complementary clockwise cyclic interval,
with its order reversed. -/
theorem mem_counterclockwise_arc_iff {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i j : GridBoundaryPosition m n) (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (counterclockwise hm hn i j).arc.support ↔
      ∃ t ≤ cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn j) (clockwiseInPortPosition hm hn i),
        x = gridBoundaryVertex (by omega) (by omega)
          (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
            (clockwiseOutPortPosition hm hn j) t) := by
  unfold counterclockwise counterclockwiseOuterArc
  rw [Walk.support_reverse, List.mem_reverse]
  exact mem_clockwise_arc_iff hm hn j i x

/-- The cyclic interval represented by a canonical choice. -/
def CanonicalInterval (choice : CanonicalChoice) {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    (x : GridVertex (m + 2) (n + 2)) : Prop :=
  match choice with
  | .clockwise =>
      ∃ t ≤ cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn i) (clockwiseInPortPosition hm hn j),
        x = gridBoundaryVertex (by omega) (by omega)
          (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
            (clockwiseOutPortPosition hm hn i) t)
  | .counterclockwise =>
      ∃ t ≤ cyclicForwardDistance (gridBoundaryLength_pos (by omega) (by omega))
          (clockwiseOutPortPosition hm hn j) (clockwiseInPortPosition hm hn i),
        x = gridBoundaryVertex (by omega) (by omega)
          (cyclicOffset (gridBoundaryLength_pos (by omega) (by omega))
            (clockwiseOutPortPosition hm hn j) t)

/-- Selecting a canonical arc selects exactly the corresponding cyclic
boundary interval. -/
theorem mem_canonical_arc_iff (choice : CanonicalChoice) {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (canonical choice hm hn i j).arc.support ↔
      CanonicalInterval choice hm hn i j x := by
  cases choice
  · exact mem_clockwise_arc_iff hm hn i j x
  · exact mem_counterclockwise_arc_iff hm hn i j x

theorem clockwise_arc_disjoint_embedded_grid {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    (v : GridVertex m n) :
    gridCollarEmbedding m n v ∉ (clockwise hm hn i j).arc.support :=
  (clockwise hm hn i j).embedded_not_mem_arc v

theorem counterclockwise_arc_disjoint_embedded_grid {m n : Nat}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (i j : GridBoundaryPosition m n)
    (v : GridVertex m n) :
    gridCollarEmbedding m n v ∉ (counterclockwise hm hn i j).arc.support :=
  (counterclockwise hm hn i j).embedded_not_mem_arc v

/-- The route from the translated end of the crosscut back to its translated
start: radial edge, selected outer arc in reverse, radial edge. -/
def closingWalk (A : GridCollarArc a b) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n b) (gridCollarEmbedding m n a) :=
  (Walk.cons A.end_spoke A.arc.reverse).concat A.start_spoke.symm

@[simp] theorem mem_support_closingWalk_iff (A : GridCollarArc a b)
    (x : GridVertex (m + 2) (n + 2)) :
    x ∈ A.closingWalk.support ↔
      x = gridCollarEmbedding m n b ∨ x ∈ A.arc.support ∨
        x = gridCollarEmbedding m n a := by
  simp [closingWalk]

/-- Apart from its two endpoints, the closing route is entirely on the outer
frame. -/
theorem boundary_of_mem_closingWalk_of_ne_endpoints (A : GridCollarArc a b)
    {x : GridVertex (m + 2) (n + 2)} (hx : x ∈ A.closingWalk.support)
    (hxb : x ≠ gridCollarEmbedding m n b)
    (hxa : x ≠ gridCollarEmbedding m n a) : IsGridBoundary x := by
  rw [mem_support_closingWalk_iff] at hx
  rcases hx with h | h | h
  · exact (hxb h).elim
  · exact A.arc_on_outer_frame x h
  · exact (hxa h).elim

/-- Every vertex of the selected arc has a position in the clockwise boundary
numbering of the collar. -/
theorem exists_boundaryPosition_of_mem_arc (A : GridCollarArc a b)
    {x : GridVertex (m + 2) (n + 2)} (hx : x ∈ A.arc.support) :
    ∃ i : GridBoundaryPosition (m + 2) (n + 2),
      gridBoundaryVertex (by omega) (by omega) i = x :=
  exists_gridBoundaryPosition (by omega) (by omega) x
    (A.arc_on_outer_frame x hx)

/-- The radial edges and a simple outer arc form a simple closing path when
the crosscut endpoints are distinct. -/
theorem closingWalk_isPath (A : GridCollarArc a b) (hab : a ≠ b) :
    A.closingWalk.IsPath := by
  rw [closingWalk, Walk.concat_isPath_iff, Walk.cons_isPath_iff]
  refine ⟨⟨A.arc_isPath.reverse, ?_⟩, ?_⟩
  · intro hb
    rw [Walk.support_reverse] at hb
    exact gridCollarEmbedding_not_boundary b
      (A.arc_on_outer_frame _ (by simpa using hb))
  · intro ha
    simp only [Walk.support_cons, List.mem_cons, Walk.support_reverse,
      List.mem_reverse] at ha
    rcases ha with heq | ha
    · apply hab
      exact (gridCollarEmbedding m n).injective heq
    · exact gridCollarEmbedding_not_boundary a (A.arc_on_outer_frame _ ha)

/-- Translate a walk in the original grid into the collar. -/
def mapWalk {u v : GridVertex m n} (p : (gridGraph m n).Walk u v) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n u) (gridCollarEmbedding m n v) :=
  p.map (gridCollarGraphEmbedding m n).toHom

@[simp] theorem support_mapWalk {u v : GridVertex m n}
    (p : (gridGraph m n).Walk u v) :
    (mapWalk p).support = p.support.map (gridCollarEmbedding m n) := by
  simp [mapWalk, gridCollarGraphEmbedding, gridCollarEmbedding]

/-- The translated crosscut and its closing route meet only at their two
common endpoints. -/
theorem mem_support_mapWalk_and_closingWalk_iff
    (A : GridCollarArc a b) (p : (gridGraph m n).Walk a b)
    (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (mapWalk p).support ∧ x ∈ A.closingWalk.support ↔
      x = gridCollarEmbedding m n a ∨ x = gridCollarEmbedding m n b := by
  constructor
  · rintro ⟨hp, hq⟩
    rw [mem_support_closingWalk_iff] at hq
    rcases hq with rfl | houter | rfl
    · exact Or.inr rfl
    · rw [support_mapWalk, List.mem_map] at hp
      obtain ⟨v, -, rfl⟩ := hp
      exact (gridCollarEmbedding_not_boundary v
        (A.arc_on_outer_frame _ houter)).elim
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · refine ⟨?_, by simp⟩
      rw [support_mapWalk, List.mem_map]
      exact ⟨a, p.start_mem_support, rfl⟩
    · refine ⟨?_, by simp⟩
      rw [support_mapWalk, List.mem_map]
      exact ⟨b, p.end_mem_support, rfl⟩

/-- Closed walk obtained by following the translated crosscut and then the
selected route through the outer collar. -/
def cycleWalk (A : GridCollarArc a b) (p : (gridGraph m n).Walk a b) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n b) (gridCollarEmbedding m n b) :=
  A.closingWalk.append (mapWalk p)

/-- The collar closure of a simple crosscut is a simple cycle.  The proof is
purely combinatorial: the translated path is internal, while the middle of the
closing path is on the outer frame. -/
theorem cycleWalk_isCycle (A : GridCollarArc a b)
    (p : (gridGraph m n).Walk a b) (hp : p.IsPath) (hab : a ≠ b) :
    (cycleWalk A p).IsCycle := by
  let r := A.arc.reverse.concat A.start_spoke.symm
  have hclose : A.closingWalk.IsPath := A.closingWalk_isPath hab
  have hr : r.IsPath := by
    exact hclose.of_cons
  have hmap : (mapWalk p).IsPath := by
    exact Walk.map_isPath_of_injective
      (gridCollarGraphEmbedding m n).injective hp
  have hrest : (r.append (mapWalk p)).IsPath := by
    rw [Walk.isPath_def, Walk.support_append]
    apply hr.support_nodup.append hmap.support_nodup.tail
    intro x hxr hxp
    have hxpa : x ≠ gridCollarEmbedding m n a := by
      intro hxa
      subst x
      have hn := hmap.support_nodup
      rw [Walk.support_eq_cons, List.nodup_cons] at hn
      exact hn.1 hxp
    have hxr' : x ∈ A.arc.support ∨ x = gridCollarEmbedding m n a := by
      simpa [r] using hxr
    rcases hxr' with houter | hxa
    · have hxpfull : x ∈ (mapWalk p).support := List.mem_of_mem_tail hxp
      rw [support_mapWalk, List.mem_map] at hxpfull
      obtain ⟨v, -, rfl⟩ := hxpfull
      exact gridCollarEmbedding_not_boundary v (A.arc_on_outer_frame _ houter)
    · exact hxpa hxa
  have hfirst_not_r :
      s(gridCollarEmbedding m n b, A.endPort) ∉ r.edges := by
    have ht := hclose.isTrail
    rw [closingWalk, Walk.concat_cons, Walk.cons_isTrail_iff] at ht
    exact ht.2
  have hfirst_not_map :
      s(gridCollarEmbedding m n b, A.endPort) ∉ (mapWalk p).edges := by
    intro he
    have hport : A.endPort ∈ (mapWalk p).support :=
      (mapWalk p).snd_mem_support_of_mem_edges he
    rw [support_mapWalk, List.mem_map] at hport
    obtain ⟨v, -, hv⟩ := hport
    exact gridCollarEmbedding_ne_of_boundary v
      (A.arc_on_outer_frame A.endPort A.arc.end_mem_support) hv
  change (Walk.cons A.end_spoke (r.append (mapWalk p))).IsCycle
  rw [Walk.cons_isCycle_iff]
  refine ⟨hrest, ?_⟩
  simp only [Walk.edges_append, List.mem_append, not_or]
  exact ⟨hfirst_not_r, hfirst_not_map⟩

/-- Exact vertex support of the collar closure. -/
theorem mem_support_cycleWalk_iff (A : GridCollarArc a b)
    (p : (gridGraph m n).Walk a b) (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (cycleWalk A p).support ↔
      (∃ v ∈ p.support, x = gridCollarEmbedding m n v) ∨ x ∈ A.arc.support := by
  rw [cycleWalk, Walk.mem_support_append_iff, mem_support_closingWalk_iff,
    support_mapWalk, List.mem_map]
  constructor
  · rintro ((rfl | hx | rfl) | ⟨v, hv, hvx⟩)
    · exact Or.inl ⟨b, p.end_mem_support, rfl⟩
    · exact Or.inr hx
    · exact Or.inl ⟨a, p.start_mem_support, rfl⟩
    · exact Or.inl ⟨v, hv, hvx.symm⟩
  · rintro (⟨v, hv, rfl⟩ | hx)
    · exact Or.inr ⟨v, hv, rfl⟩
    · exact Or.inl (Or.inr (Or.inl hx))

/-- A collar closure contains exactly the translated vertices of the original
grid that occur on the crosscut. -/
theorem mem_cycleWalk_and_collar_range_iff (A : GridCollarArc a b)
    (p : (gridGraph m n).Walk a b) (v : GridVertex m n) :
    gridCollarEmbedding m n v ∈ (cycleWalk A p).support ↔ v ∈ p.support := by
  rw [mem_support_cycleWalk_iff]
  constructor
  · rintro (⟨w, hw, heq⟩ | houter)
    · exact (gridCollarEmbedding m n).injective heq ▸ hw
    · exact (gridCollarEmbedding_not_boundary v
        (A.arc_on_outer_frame _ houter)).elim
  · intro hv
    exact Or.inl ⟨v, hv, rfl⟩

end GridCollarArc

/-- A simple grid path between distinct boundary vertices whose only boundary
contacts are its endpoints. -/
structure GridCrosscut (m n : Nat) where
  start : GridVertex m n
  finish : GridVertex m n
  path : (gridGraph m n).Walk start finish
  isPath : path.IsPath
  start_ne_finish : start ≠ finish
  start_boundary : IsGridBoundary start
  finish_boundary : IsGridBoundary finish
  boundary_contact : ∀ v ∈ path.support,
    IsGridBoundary v → v = start ∨ v = finish

namespace GridCrosscut

variable {m n : Nat}

/-- Boundary position of the initial endpoint of a crosscut. -/
noncomputable def startPosition (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    GridBoundaryPosition m n :=
  (gridBoundaryEquiv hm hn).symm ⟨P.start, P.start_boundary⟩

/-- Boundary position of the terminal endpoint of a crosscut. -/
noncomputable def finishPosition (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    GridBoundaryPosition m n :=
  (gridBoundaryEquiv hm hn).symm ⟨P.finish, P.finish_boundary⟩

@[simp] theorem boundaryVertex_startPosition (P : GridCrosscut m n)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    gridBoundaryVertex hm hn (P.startPosition hm hn) = P.start := by
  exact congrArg Subtype.val
    ((gridBoundaryEquiv hm hn).apply_symm_apply ⟨P.start, P.start_boundary⟩)

@[simp] theorem boundaryVertex_finishPosition (P : GridCrosscut m n)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    gridBoundaryVertex hm hn (P.finishPosition hm hn) = P.finish := by
  exact congrArg Subtype.val
    ((gridBoundaryEquiv hm hn).apply_symm_apply ⟨P.finish, P.finish_boundary⟩)

/-- The canonical clockwise collar arc of a crosscut. -/
noncomputable def clockwiseArc (P : GridCrosscut m n) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    GridCollarArc P.start P.finish := by
  rw [← P.boundaryVertex_startPosition hm hn,
    ← P.boundaryVertex_finishPosition hm hn]
  exact GridCollarArc.clockwise hm hn (P.startPosition hm hn) (P.finishPosition hm hn)

/-- The canonical counterclockwise collar arc of a crosscut. -/
noncomputable def counterclockwiseArc (P : GridCrosscut m n)
    (hm : 2 ≤ m) (hn : 2 ≤ n) : GridCollarArc P.start P.finish := by
  rw [← P.boundaryVertex_startPosition hm hn,
    ← P.boundaryVertex_finishPosition hm hn]
  exact GridCollarArc.counterclockwise hm hn
    (P.startPosition hm hn) (P.finishPosition hm hn)

/-- Select either canonical cyclic boundary interval without supplying an arc. -/
noncomputable def canonicalArc (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    GridCollarArc P.start P.finish :=
  match choice with
  | .clockwise => P.clockwiseArc hm hn
  | .counterclockwise => P.counterclockwiseArc hm hn

/-- Closed walk obtained from either canonical boundary interval. -/
noncomputable def canonicalClosedWalk (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n P.finish) (gridCollarEmbedding m n P.finish) :=
  (P.canonicalArc choice hm hn).cycleWalk P.path

/-- Both canonical closures are simple cycles. -/
theorem canonicalClosedWalk_isCycle (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (P.canonicalClosedWalk choice hm hn).IsCycle :=
  (P.canonicalArc choice hm hn).cycleWalk_isCycle
    P.path P.isPath P.start_ne_finish

/-- A canonical closure intersects the embedded original grid exactly in the
given crosscut. -/
theorem mem_canonicalClosedWalk_collar_iff (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n) :
    gridCollarEmbedding m n v ∈ (P.canonicalClosedWalk choice hm hn).support ↔
      v ∈ P.path.support :=
  (P.canonicalArc choice hm hn).mem_cycleWalk_and_collar_range_iff P.path v

/-- The no-internal-boundary-contact hypothesis gives exactly the two original
boundary contacts for either canonical closure. -/
theorem mem_canonicalClosedWalk_of_original_boundary_iff (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n) (hv : IsGridBoundary v) :
    gridCollarEmbedding m n v ∈ (P.canonicalClosedWalk choice hm hn).support ↔
      v = P.start ∨ v = P.finish := by
  rw [P.mem_canonicalClosedWalk_collar_iff choice hm hn]
  constructor
  · intro h
    exact P.boundary_contact v h hv
  · rintro (rfl | rfl)
    · exact P.path.start_mem_support
    · exact P.path.end_mem_support

/-- The chosen canonical outer interval is internally disjoint from every
embedded original-grid vertex. -/
theorem canonicalArc_disjoint_embedded_grid (P : GridCrosscut m n)
    (choice : GridCollarArc.CanonicalChoice) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n) :
    gridCollarEmbedding m n v ∉ (P.canonicalArc choice hm hn).arc.support :=
  (P.canonicalArc choice hm hn).embedded_not_mem_arc v

/-- Close a crosscut using a selected arc of the outer collar. -/
def closedWalk (P : GridCrosscut m n) (A : GridCollarArc P.start P.finish) :
    (gridGraph (m + 2) (n + 2)).Walk
      (gridCollarEmbedding m n P.finish) (gridCollarEmbedding m n P.finish) :=
  A.cycleWalk P.path

/-- A crosscut closed along a selected simple perimeter arc is a simple cycle. -/
theorem closedWalk_isCycle (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) : (P.closedWalk A).IsCycle :=
  A.cycleWalk_isCycle P.path P.isPath P.start_ne_finish

/-- The closed cycle meets the translated original grid exactly in the
translated crosscut. -/
theorem mem_closedWalk_collar_iff (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) (v : GridVertex m n) :
    gridCollarEmbedding m n v ∈ (P.closedWalk A).support ↔ v ∈ P.path.support :=
  A.mem_cycleWalk_and_collar_range_iff P.path v

/-- Consequently, among translated vertices of the original boundary, the
cycle has exactly the two prescribed contacts. -/
theorem mem_closedWalk_of_original_boundary_iff (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) (v : GridVertex m n)
    (hv : IsGridBoundary v) :
    gridCollarEmbedding m n v ∈ (P.closedWalk A).support ↔
      v = P.start ∨ v = P.finish := by
  rw [P.mem_closedWalk_collar_iff A]
  constructor
  · intro h
    exact P.boundary_contact v h hv
  · rintro (rfl | rfl)
    · exact P.path.start_mem_support
    · exact P.path.end_mem_support

/-- Full support description: translated crosscut vertices together with the
chosen outer perimeter arc. -/
theorem mem_closedWalk_iff (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish)
    (x : GridVertex (m + 2) (n + 2)) :
    x ∈ (P.closedWalk A).support ↔
      (∃ v ∈ P.path.support, x = gridCollarEmbedding m n v) ∨
        x ∈ A.arc.support :=
  A.mem_support_cycleWalk_iff P.path x

/-- Faces cut off from the unbounded face by the combinatorially constructed
cycle, using the dual reachability API.  No nonemptiness claim is made here. -/
def interiorFaces (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) : Finset (GridFace (m + 2) (n + 2)) :=
  cycleInteriorFaces (P.closedWalk A)

@[simp] theorem out_not_mem_interiorFaces (P : GridCrosscut m n)
    (A : GridCollarArc P.start P.finish) :
    GridFace.out ∉ P.interiorFaces A :=
  out_not_mem_cycleInteriorFaces (P.closedWalk A)

end GridCrosscut

end GridGraphs
