import GridGraphs.ResidueZeroBase
import GridGraphs.ResidueZeroBridge
import GridGraphs.ResidueZeroInduction

/-!
# Persistent residue-zero paths

The graph in this file strengthens `widenableOldDualGraph` by recording, on
every edge, that both endpoint rows are strictly interior.  This is precisely
the hypothesis needed by `widenableOldDualGraph_interior_adj_widen`.
-/

namespace GridGraphs

open SimpleGraph

/-- A bounded coordinate lies in a strict interior face row. -/
def IsStrictInteriorResidueZeroCoord (k : Nat)
    (x : Fin (3 * k - 1) × Fin (3 * k - 1)) : Prop :=
  0 < x.1.val ∧ x.1.val < 3 * k - 2

/-- Widenable edges whose two endpoint rows are both strictly interior. -/
def persistentResidueZeroGraph (k : Nat) (hk : 7 ≤ k) :
    SimpleGraph (Fin (3 * k - 1) × Fin (3 * k - 1)) where
  Adj x y :=
    (widenableOldDualGraph k hk).Adj x y ∧
      IsStrictInteriorResidueZeroCoord k x ∧
      IsStrictInteriorResidueZeroCoord k y
  symm := by
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy.symm, hy, hx⟩
  loopless := by
    rintro x ⟨hxx, -⟩
    exact (widenableOldDualGraph k hk).loopless x hxx

/-- Every strict interior coordinate reaches the bounded anchor using only
edges which retain the interior-row invariant. -/
def PersistentResidueZeroCertificate (k : Nat) (hk : 7 ≤ k) : Prop :=
  ∀ (r : Fin (3 * k - 1)), 0 < r.val → r.val < 3 * k - 2 →
    ∀ c : Fin (3 * k - 1),
      (persistentResidueZeroGraph k hk).Reachable (r, c)
        (residueZeroAnchorCoord k hk)

/-- Forgetting endpoint interiority gives the original widenable graph. -/
def persistentResidueZeroToWidenable (k : Nat) (hk : 7 ≤ k) :
    persistentResidueZeroGraph k hk →g widenableOldDualGraph k hk where
  toFun := id
  map_rel' h := h.1

private def persistentTable (xs : List Nat) (c fallback : Nat) : Nat :=
  xs[c]?.getD fallback

private def persistentBaseParentDirection (r c : Nat) : Nat :=
  match r with
  | 1 => persistentTable [3,1,2, 3,1,2, 3,1,2, 3,1,2, 3,3,1, 1,2,3, 1,2] c 4
  | 2 => persistentTable [3,1,2, 3,1,2, 3,1,2, 3,3,1, 3,0,3, 1,2,3, 1,2] c 4
  | 3 => persistentTable [3,1,2, 3,1,2, 3,3,1, 3,0,3, 0,2,3, 1,2,3, 1,2] c 4
  | 4 => persistentTable [3,1,2, 3,1,2, 3,0,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 5 => persistentTable [3,1,2, 3,3,1, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 6 => persistentTable [3,3,1, 3,0,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 7 => persistentTable [3,0,3, 0,2,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 8 => persistentTable [3,1,3, 0,2,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 9 => persistentTable [3,3,0, 0,2,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 10 => persistentTable [3,0,2, 3,1,3, 1,2,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 11 => persistentTable [3,0,2, 3,3,0, 3,1,3, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 12 => persistentTable [3,0,2, 3,0,2, 3,3,0, 0,2,3, 0,2,3, 1,2,3, 1,2] c 4
  | 13 => persistentTable [3,0,2, 3,0,2, 3,0,2, 3,1,3, 0,2,3, 1,2,3, 1,2] c 4
  | 14 => persistentTable [3,0,2, 3,0,2, 3,0,2, 3,3,0, 0,2,3, 1,2,3, 1,2] c 4
  | 15 => persistentTable [3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,1,3, 1,2,3, 1,2] c 4
  | 16 => persistentTable [3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,3,0, 3,1,3, 1,2] c 4
  | 17 => persistentTable [3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,3,0, 3,1] c 4
  | 18 => persistentTable [3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,0,2, 3,4] c 4
  | _ => 4

private theorem persistentBaseParentDirection_eq (r c : Nat) :
    residueZeroBaseParentDirection r c = persistentBaseParentDirection r c :=
  rfl

set_option maxHeartbeats 2000000 in
private theorem residueZeroBaseParent_strictInterior
    (x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1))
    (hr0 : 0 < x.1.val) (hrlast : x.1.val < 3 * 7 - 2) :
    IsStrictInteriorResidueZeroCoord 7 (residueZeroBaseParent x) := by
  rcases x with ⟨r, c⟩
  fin_cases r
  all_goals fin_cases c
  all_goals try { norm_num at hr0 }
  all_goals try { norm_num at hrlast }
  all_goals norm_num [IsStrictInteriorResidueZeroCoord, residueZeroBaseParent,
    persistentBaseParentDirection_eq, persistentBaseParentDirection, persistentTable]

/-- A non-root base parent edge belongs to the persistent graph. -/
theorem residueZeroBaseParent_persistent_adj
    (x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1))
    (hr0 : 0 < x.1.val) (hrlast : x.1.val < 3 * 7 - 2)
    (hne : x ≠ residueZeroAnchorCoord 7 (by omega)) :
    (persistentResidueZeroGraph 7 (by omega)).Adj x
      (residueZeroBaseParent x) := by
  exact ⟨residueZeroBaseParent_adj x hr0 hrlast hne,
    ⟨hr0, hrlast⟩, residueZeroBaseParent_strictInterior x hr0 hrlast⟩

/-- The explicit parent/rank tree proves the persistent width-seven base. -/
theorem persistentResidueZeroCertificate_seven :
    PersistentResidueZeroCertificate 7 (by omega) := by
  intro r hr0 hrlast c
  let x : Fin (3 * 7 - 1) × Fin (3 * 7 - 1) := (r, c)
  have main : ∀ n y, residueZeroBaseRank y = n →
      IsStrictInteriorResidueZeroCoord 7 y →
      (persistentResidueZeroGraph 7 (by omega)).Reachable y
        (residueZeroAnchorCoord 7 (by omega)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro y hyrank hy
        by_cases hanchor : y = residueZeroAnchorCoord 7 (by omega)
        · simpa [hanchor] using
            (Reachable.refl : (persistentResidueZeroGraph 7 (by omega)).Reachable
              (residueZeroAnchorCoord 7 (by omega))
              (residueZeroAnchorCoord 7 (by omega)))
        · have hlt := residueZeroBaseRank_parent_lt y hy.1 hy.2 hanchor
          have hp := residueZeroBaseParent_strictInterior y hy.1 hy.2
          exact (residueZeroBaseParent_persistent_adj y hy.1 hy.2 hanchor).reachable.trans
            (ih (residueZeroBaseRank (residueZeroBaseParent y)) (by omega)
              (residueZeroBaseParent y) rfl hp)
  exact main (residueZeroBaseRank x) x rfl ⟨hr0, hrlast⟩

/-- Coordinate widening is a graph homomorphism for the corrected invariant. -/
def persistentResidueZeroWidenHom (k : Nat) (hk : 7 ≤ k) :
    persistentResidueZeroGraph k hk →g
      persistentResidueZeroGraph (k + 1) (by omega) where
  toFun := widenBoundedFace k
  map_rel' := by
    intro x y h
    refine ⟨widenableOldDualGraph_interior_adj_widen k hk x y
      h.2.1.1 h.2.1.2 h.2.2.1 h.2.2.2 h.1, ?_, ?_⟩
    · simp [IsStrictInteriorResidueZeroCoord, widenBoundedFace]
      omega
    · simp [IsStrictInteriorResidueZeroCoord, widenBoundedFace]
      omega

/-- A persistent old path maps to a persistent successor path. -/
theorem persistent_reachable_widen {k : Nat} {hk : 7 ≤ k}
    {x y : Fin (3 * k - 1) × Fin (3 * k - 1)}
    (h : (persistentResidueZeroGraph k hk).Reachable x y) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (widenBoundedFace k x) (widenBoundedFace k y) :=
  h.map (persistentResidueZeroWidenHom k hk)

/-!
The complement of the widened old rectangle has exactly three coordinate
families.  The fourth field below is the route from the widened old anchor to
the new anchor.  Keeping these obligations separate prevents a proof from
discarding the persistent-edge invariant at the anchor bridge.
-/

/-- Exact geometric obligations for one persistent successor step. -/
structure PersistentResidueZeroStepGeometry (k : Nat) (hk : 7 ≤ k) : Prop where
  topRows :
    ∀ (r c : Fin (3 * (k + 1) - 1)),
      (r.val = 1 ∨ r.val = 2) →
      (persistentResidueZeroGraph (k + 1) (by omega)).Reachable (r, c)
        (residueZeroAnchorCoord (k + 1) (by omega))
  rightSlab :
    ∀ (r c : Fin (3 * (k + 1) - 1)),
      3 ≤ r.val → r.val < 3 * k → 3 * k - 1 ≤ c.val →
      (persistentResidueZeroGraph (k + 1) (by omega)).Reachable (r, c)
        (residueZeroAnchorCoord (k + 1) (by omega))
  appendedRow :
    ∀ c : Fin (3 * (k + 1) - 1),
      (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
        (⟨3 * k, by omega⟩, c)
        (residueZeroAnchorCoord (k + 1) (by omega))
  anchorBridge :
    (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (widenBoundedFace k (residueZeroAnchorCoord k hk))
      (residueZeroAnchorCoord (k + 1) (by omega))

/-- Old paths map through the homomorphism; the three new coordinate regions
and the anchor bridge are routed by the corresponding geometric fields. -/
theorem PersistentResidueZeroCertificate.succ
    {k : Nat} {hk : 7 ≤ k}
    (hold : PersistentResidueZeroCertificate k hk)
    (hgeom : PersistentResidueZeroStepGeometry k hk) :
    PersistentResidueZeroCertificate (k + 1) (by omega) := by
  intro r hr0 hrlast c
  by_cases htop : r.val ≤ 2
  · exact hgeom.topRows r c (by omega)
  by_cases happended : r.val = 3 * k
  · convert hgeom.appendedRow c using 1
    apply Prod.ext
    · exact Fin.ext happended
    · rfl
  by_cases hright : 3 * k - 1 ≤ c.val
  · exact hgeom.rightSlab r c (by omega) (by omega) hright
  · let r₀ : Fin (3 * k - 1) := ⟨r.val - 2, by omega⟩
    let c₀ : Fin (3 * k - 1) := ⟨c.val, by omega⟩
    have hr₀0 : 0 < r₀.val := by simp [r₀]; omega
    have hr₀last : r₀.val < 3 * k - 2 := by simp [r₀]; omega
    have hcoord : widenBoundedFace k (r₀, c₀) = (r, c) := by
      apply Prod.ext <;> apply Fin.ext <;> simp [widenBoundedFace, r₀, c₀]
      omega
    rw [← hcoord]
    exact (persistent_reachable_widen (hold r₀ hr₀0 hr₀last c₀)).trans
      hgeom.anchorBridge

/-- Conditional induction, isolating exactly the geometric work not supplied
by the imported widening API. -/
theorem persistentResidueZeroCertificate_of_stepGeometry
    (hgeom : ∀ k (hk : 7 ≤ k), PersistentResidueZeroStepGeometry k hk)
    (k : Nat) (hk : 7 ≤ k) : PersistentResidueZeroCertificate k hk := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simpa using persistentResidueZeroCertificate_seven
  | succ d ih =>
      simpa [Nat.add_assoc] using
        PersistentResidueZeroCertificate.succ (ih (by omega))
          (hgeom (7 + d) (by omega))

/-- The corrected certificate implies the existing anchored certificate. -/
theorem PersistentResidueZeroCertificate.toAnchored
    {k : Nat} {hk : 7 ≤ k}
    (h : PersistentResidueZeroCertificate k hk) :
    ResidueZeroAnchoredCertificate k hk := by
  apply residueZeroAnchoredCertificate_mk k hk
  intro r hr0 hrlast c
  exact (h r hr0 hrlast c).map (persistentResidueZeroToWidenable k hk)

/-- The target lower bound follows directly through the existing consequence
of an anchored certificate. -/
theorem residueZero_le_maxPreserved_of_persistent
    (k : Nat) (hk : 7 ≤ k) (h : PersistentResidueZeroCertificate k hk) :
    3 * k ^ 2 + 3 * k - 2 ≤ maxPreserved (3 * k) (3 * k) :=
  residueZero_le_maxPreserved_of_anchored k hk h.toAnchored

end GridGraphs
