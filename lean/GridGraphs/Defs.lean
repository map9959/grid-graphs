import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
-- Removed: import Mathlib.Data.Finset.Nat (module no longer exists or renamed in current mathlib)

namespace GridGraphs

/-- Number of vertices in m×n grid. -/
@[simp] def numVerts (m n : Nat) : Nat := m * n

/-- Number of horizontal edges. -/
@[simp] def numHoriz (m n : Nat) : Nat := m * (n - 1)
/-- Number of vertical edges. -/
@[simp] def numVert (m n : Nat) : Nat := n * (m - 1)

/-! Total edges in grid graph. -/
@[simp] def numEdges (m n : Nat) : Nat := numHoriz m n + numVert m n

lemma numEdges_eq (m n : Nat) : numEdges m n = m*(n-1) + n*(m-1) := by
  simp [numEdges, numHoriz, numVert]

/-- Degree sum over all vertices of grid via 2|E|. -/
@[simp] def degSumGrid (m n : Nat) : Nat := 2 * numEdges m n

/-- Degree sum of any spanning tree on mn vertices: 2(|V|-1). -/
@[simp] def degSumTree (m n : Nat) : Nat := 2 * (numVerts m n - 1)

/-- Total deficiency independent of chosen spanning tree. -/
@[simp] def deficiency (m n : Nat) : Nat := degSumGrid m n - degSumTree m n

/-! Algebraic helper lemmas for the succ-succ deficiency case. -/

lemma succ_mul_succ_sub_one (a b : Nat) : (a+1)*(b+1) - 1 = a*b + a + b := by
  have h : (a+1)*(b+1) = a*b + a + b + 1 := by ring
  omega

/-- The deficiency of the (m+1)×(n+1) grid is `2*m*n`. Proven by direct Nat
arithmetic from the definitions, after fully unfolding to a pure linear
arithmetic goal in the atom `m*n` (treated by omega as an opaque Nat). -/
lemma deficiency_succ_succ (m n : Nat) : deficiency (m+1) (n+1) = 2 * m * n := by
  -- Compute every constituent term as an explicit polynomial in m,n.
  have hV  : numVerts (m+1) (n+1) = m*n + m + n + 1 := by
    unfold numVerts; ring
  have hH  : numHoriz (m+1) (n+1) = m*n + n := by
    show (m+1) * ((n+1) - 1) = m*n + n
    have : (n+1) - 1 = n := rfl
    rw [this]; ring
  have hVe : numVert (m+1) (n+1) = m*n + m := by
    show (n+1) * ((m+1) - 1) = m*n + m
    have : (m+1) - 1 = m := rfl
    rw [this]; ring
  have hE  : numEdges (m+1) (n+1) = 2*(m*n) + m + n := by
    unfold numEdges; rw [hH, hVe]; ring
  -- Now expand `deficiency`.
  unfold deficiency degSumGrid degSumTree
  rw [hE, hV]
  -- Goal: 2*(2*(m*n) + m + n) - 2*(m*n + m + n + 1 - 1) = 2*m*n
  -- omega handles linear arithmetic over the opaque atom `m*n`.
  have key : 2 * m * n = 2 * (m * n) := by ring
  rw [key]
  omega

lemma deficiency_closed_form (m n : Nat) : deficiency m n = 2 * (m - 1) * (n - 1) := by
  cases m with
  | zero =>
    cases n with
    | zero => simp [deficiency]
    | succ n' => simp [deficiency]
  | succ m' =>
    cases n with
    | zero => simp [deficiency]
    | succ n' =>
      simpa [Nat.succ_sub_one] using deficiency_succ_succ m' n'

/-- Count of corner vertices. -/
@[simp] def numCorners (m n : Nat) : Nat :=
  match m, n with
  | 0, _ => 0
  | _, 0 => 0
  | 1, 1 => 1
  | 1, _ => 2
  | _, 1 => 2
  | _, _ => 4

/-- Count of border (non-corner) vertices. -/
@[simp] def numBorderNonCorner (m n : Nat) : Nat :=
  match m, n with
  | 0, _ => 0
  | _, 0 => 0
  | 1, 1 => 0
  | 1, Nat.succ (Nat.succ k) => (Nat.succ (Nat.succ k)) - 2
  | Nat.succ (Nat.succ k), 1 => (Nat.succ (Nat.succ k)) - 2
  | Nat.succ (Nat.succ k), Nat.succ (Nat.succ l) =>
      let mVal := Nat.succ (Nat.succ k)
      let nVal := Nat.succ (Nat.succ l)
      2*mVal + 2*nVal - 8

@[simp] def numInterior (m n : Nat) : Nat := if m < 3 || n < 3 then 0 else (m - 2) * (n - 2)

/-- Vertex type for m×n grid graph: pairs of finite indices. -/
def GridVertex (m n : Nat) := Fin m × Fin n

/-! Simple graph definition.
We provide a minimal adjacency predicate directly (no Finset edge set needed).
-/
/-- Adjacency (undirected) for the grid: differ by exactly 1 in one coordinate, equal in the other. -/
def adjacent (m n : Nat) (v w : GridVertex m n) : Prop :=
  ((v.1 = w.1) ∧ ((v.2.val + 1 = w.2.val) ∨ (w.2.val + 1 = v.2.val))) ∨
  ((v.2 = w.2) ∧ ((v.1.val + 1 = w.1.val) ∨ (w.1.val + 1 = v.1.val)))

/-- The (simple) grid graph on an m×n grid. -/
def gridGraph (m n : Nat) : SimpleGraph (GridVertex m n) :=
{ Adj := adjacent m n
  symm := by
    intro v w h; unfold adjacent at h; unfold adjacent;
    rcases h with h | h
    · rcases h with ⟨hrow, hdiff⟩;
      left; constructor;
      · simpa using hrow.symm
      · rcases hdiff with h1 | h1;
        · right; simpa using h1
        · left; simpa using h1
    · rcases h with ⟨hcol, hdiff⟩;
      right; constructor;
      · simpa using hcol.symm
      · rcases hdiff with h1 | h1;
        · right; simpa using h1
        · left; simpa using h1
  loopless := by
    intro v h
    unfold adjacent at h
    rcases h with h | h
    · rcases h with ⟨_, hdiff⟩; rcases hdiff with h1 | h1
      · exact Nat.succ_ne_self _ h1
      · exact Nat.succ_ne_self _ h1
    · rcases h with ⟨_, hdiff⟩; rcases hdiff with h1 | h1
      · exact Nat.succ_ne_self _ h1
      · exact Nat.succ_ne_self _ h1 }

/--- Degree of a vertex in the grid graph (stub; returns 0). TODO: implement enumeration. -/
def gridDegree (m n : Nat) (_v : GridVertex m n) : Nat := 0

/-- Maximum possible degree of a vertex in the grid graph. -/
def maxGridDegree (m n : Nat) (v : GridVertex m n) : Nat :=
  match m, n with
  | 0, _ => 0
  | _, 0 => 0
  | 1, 1 => 2  -- corner vertex in 1×1 grid
  | 1, _ => if v.1.val = 0 ∨ v.1.val = 0 then 1 else 2  -- border vertices in 1×n grid
  | _, 1 => if v.2.val = 0 ∨ v.2.val = 0 then 1 else 2  -- border vertices in m×1 grid
  | _, _ =>
    if (v.1.val = 0 ∨ v.1.val = m - 1) ∧ (v.2.val = 0 ∨ v.2.val = n - 1) then
      -- corner vertex
      2
    else if v.1.val = 0 ∨ v.1.val = m - 1 ∨ v.2.val = 0 ∨ v.2.val = n - 1 then
      -- border (non-corner) vertex
      3
    else
      -- interior vertex
      4

/-! Preservation predicates (stubs while API updated).

In this codebase a vertex is **preserved** in a spanning tree `T` iff it is
**full-degree**, i.e. `deg_T(v) = deg_G(v)`. The two terms are interchangeable;
"preserved" follows the terminology of `docs/DERIVATION.md`. -/

/-- A vertex `v` is *preserved* (equivalently, *full-degree*) in a spanning
tree `T` of the grid graph iff every grid edge incident to `v` lies in `T`,
i.e. `deg_T(v) = deg_G(v)`. (Currently a stub returning `True` while the
spanning-tree API is being introduced.) -/
def isPreserved (m n : Nat) (_T : SimpleGraph (GridVertex m n)) (_v : GridVertex m n) : Prop := True

/-- Deficiency of a vertex in a spanning tree: difference between its grid
degree and its tree degree. A vertex is preserved (full-degree) iff its
deficiency is 0. -/
def vertexDeficiency (m n : Nat) (_T : SimpleGraph (GridVertex m n)) (_v : GridVertex m n) : Nat := 0

/-- Count of preserved (full-degree) vertices in a spanning tree `T`. -/
def numPreserved (m n : Nat) (_T : SimpleGraph (GridVertex m n)) : Nat := numVerts m n -- stub

/-- Maximum number of preserved (full-degree) vertices over all spanning
trees of the m × n grid graph. This is the quantity `P(m, n)` analyzed in
`docs/DERIVATION.md` and `EVIDENCE.md`. -/
def maxPreserved (m n : Nat) : Nat := numVerts m n -- stub

/-! ### Vertex-class partition

The three vertex categories `numCorners`, `numBorderNonCorner`, `numInterior`
exhaust the `m × n` vertex set. Established by case analysis on the
`{0, 1, ≥2}` shape of `m` and `n`, matching the underlying definitions. -/

lemma verts_partition (m n : Nat) :
    numCorners m n + numBorderNonCorner m n + numInterior m n = numVerts m n := by
  -- Case split that mirrors the pattern-matching of the count definitions.
  match m, n with
  | 0, n =>
    simp [numCorners, numBorderNonCorner, numInterior, numVerts]
  | Nat.succ m', 0 =>
    simp [numCorners, numBorderNonCorner, numInterior, numVerts]
  | 1, 1 =>
    decide
  | 1, Nat.succ (Nat.succ k) =>
    -- 1 × (k+2) row: 2 corners + k border + 0 interior = k + 2 = numVerts.
    show 2 + ((k + 2) - 2) + (if 1 < 3 || (k+2) < 3 then 0 else (1-2) * ((k+2)-2))
        = 1 * (k + 2)
    have h : (1 < 3 || (k+2) < 3) = true := by simp
    simp only [h, if_true]
    omega
  | Nat.succ (Nat.succ k), 1 =>
    -- (k+2) × 1 column: 2 corners + k border + 0 interior = k + 2 = numVerts.
    show 2 + ((k + 2) - 2) + (if (k+2) < 3 || 1 < 3 then 0 else ((k+2)-2) * (1-2))
        = (k + 2) * 1
    have h : ((k+2) < 3 || 1 < 3) = true := by simp
    simp only [h, if_true]
    omega
  | Nat.succ (Nat.succ k), Nat.succ (Nat.succ l) =>
    -- (k+2) × (l+2) grid: 4 corners + (2(k+2) + 2(l+2) - 8) border
    -- + (k * l) interior = (k+2)(l+2).
    show 4 + (2 * (k + 2) + 2 * (l + 2) - 8)
        + (if (k+2) < 3 || (l+2) < 3 then 0 else ((k+2) - 2) * ((l+2) - 2))
        = (k + 2) * (l + 2)
    -- The interior `if` condition is false only when both arms are ≥ 3, i.e.
    -- `k ≥ 1` and `l ≥ 1`. Split on `k = 0` and `l = 0`.
    rcases k with _ | k'
    · rcases l with _ | l'
      · -- m = 2, n = 2: 4 corners only.
        decide
      · -- m = 2, n = l' + 3: zero interior (m < 3).
        have hcond : ((0:Nat) + 2 < 3 || (l' + 1 + 2) < 3) = true := by simp
        simp only [hcond, if_true]
        omega
    · rcases l with _ | l'
      · -- m = k' + 3, n = 2: zero interior (n < 3).
        have hcond : ((k' + 1 + 2) < 3 || (0:Nat) + 2 < 3) = true := by simp
        simp only [hcond, if_true]
        omega
      · -- m = k' + 3, n = l' + 3 (both ≥ 3): full interior contributes.
        have hcond_false : ((k' + 1 + 2) < 3 || (l' + 1 + 2) < 3) = false := by
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
          exact ⟨by omega, by omega⟩
        rw [hcond_false]
        -- The remaining `if false = true then ... else ...` reduces because
        -- `false = true` is `False` propositionally; `simp` handles it.
        simp only [Bool.false_eq_true, ite_false]
        -- Reduce the surviving Nat subtractions.
        have hm2 : (k' + 1 + 2) - 2 = k' + 1 := by omega
        have hn2 : (l' + 1 + 2) - 2 = l' + 1 := by omega
        have hborder : 2 * (k' + 1 + 2) + 2 * (l' + 1 + 2) - 8
            = 2 * k' + 2 * l' + 4 := by omega
        rw [hm2, hn2, hborder]
        ring

end GridGraphs
