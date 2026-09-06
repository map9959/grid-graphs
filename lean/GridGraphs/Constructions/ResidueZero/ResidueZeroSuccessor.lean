import GridGraphs.Constructions.ResidueZero.ResidueZeroPersistent
import GridGraphs.Constructions.ResidueZero.ResidueZeroPersistentSlab
import GridGraphs.Constructions.ResidueZero.ResidueZeroPersistentBridge
import GridGraphs.Constructions.ResidueZero.ResidueZeroFrontier
import GridGraphs.Constructions.ResidueZero.ResidueZeroWord

/-!
# The persistent residue-zero successor

The new top and appended rows need not be routed all the way to the successor
anchor.  It is enough to attach each of their faces to some widened strict
interior old face.  The old certificate then supplies the rest of the route.

This file also records the pointwise version of the column-attachment argument.
Unlike `DualFaceRowsAttached`, it does not assume that an entire frontier is
already connected.
-/

namespace GridGraphs

open SimpleGraph

/-- A successor face attaches to some widened strict interior old face. -/
def AttachesToWidenedOldInterior (k : Nat) (hk : 7 ≤ k)
    (x : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1)) : Prop :=
  ∃ (r₀ : Fin (3 * k - 1)), 0 < r₀.val ∧ r₀.val < 3 * k - 2 ∧
    ∃ c₀ : Fin (3 * k - 1),
      (persistentResidueZeroGraph (k + 1) (by omega)).Reachable x
        (widenBoundedFace k (r₀, c₀))

/-- Successor geometry with local attachment, rather than global reachability,
for the two new endpoint families. -/
structure BetterPersistentResidueZeroStepGeometry
    (k : Nat) (hk : 7 ≤ k) : Prop where
  topRows :
    ∀ (r c : Fin (3 * (k + 1) - 1)),
      (r.val = 1 ∨ r.val = 2) →
      AttachesToWidenedOldInterior k hk (r, c)
  rightSlab :
    ∀ (r c : Fin (3 * (k + 1) - 1)),
      3 ≤ r.val → r.val < 3 * k → 3 * k - 1 ≤ c.val →
      (persistentResidueZeroGraph (k + 1) (by omega)).Reachable (r, c)
        (residueZeroAnchorCoord (k + 1) (by omega))
  appendedRow :
    ∀ c : Fin (3 * (k + 1) - 1),
      AttachesToWidenedOldInterior k hk (⟨3 * k, by omega⟩, c)
  anchorBridge :
    (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (widenBoundedFace k (residueZeroAnchorCoord k hk))
      (residueZeroAnchorCoord (k + 1) (by omega))

/-- An attachment is completed by the widened old certificate and the direct
anchor bridge. -/
theorem AttachesToWidenedOldInterior.reachable_anchor
    {k : Nat} {hk : 7 ≤ k}
    (hold : PersistentResidueZeroCertificate k hk)
    (hbridge : (persistentResidueZeroGraph (k + 1) (by omega)).Reachable
      (widenBoundedFace k (residueZeroAnchorCoord k hk))
      (residueZeroAnchorCoord (k + 1) (by omega)))
    {x : Fin (3 * (k + 1) - 1) × Fin (3 * (k + 1) - 1)}
    (hx : AttachesToWidenedOldInterior k hk x) :
    (persistentResidueZeroGraph (k + 1) (by omega)).Reachable x
      (residueZeroAnchorCoord (k + 1) (by omega)) := by
  rcases hx with ⟨r₀, hr₀0, hr₀last, c₀, hx⟩
  exact hx.trans ((persistent_reachable_widen
    (hold r₀ hr₀0 hr₀last c₀)).trans hbridge)

/-- The improved successor theorem.  Only the genuinely new faces require a
local route to an existential old coordinate. -/
theorem PersistentResidueZeroCertificate.succ_of_betterGeometry
    {k : Nat} {hk : 7 ≤ k}
    (hold : PersistentResidueZeroCertificate k hk)
    (hgeom : BetterPersistentResidueZeroStepGeometry k hk) :
    PersistentResidueZeroCertificate (k + 1) (by omega) := by
  intro r hr0 hrlast c
  by_cases htop : r.val ≤ 2
  · exact (hgeom.topRows r c (by omega)).reachable_anchor hold hgeom.anchorBridge
  by_cases happended : r.val = 3 * k
  · have hattach := hgeom.appendedRow c
    have hroute := hattach.reachable_anchor hold hgeom.anchorBridge
    convert hroute using 1
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

/-- Pointwise column attachment.  This is the part of `attach_all_columns`
which does not use connectedness of the outer frontier. -/
theorem attach_all_columns_pointwise {V : Type*} {G : SimpleGraph V} {k : Nat}
    (hk : 1 ≤ k) (outer middle : Fin (3 * k - 1) → V)
    (hpair : ∀ q (hq : q < k),
      (G.Reachable (outer ⟨3 * q, by omega⟩) (middle ⟨3 * q, by omega⟩) ∨
        G.Reachable (outer ⟨3 * q + 1, by omega⟩)
          (middle ⟨3 * q + 1, by omega⟩)) ∧
      G.Adj (middle ⟨3 * q, by omega⟩) (middle ⟨3 * q + 1, by omega⟩))
    (hgap : ∀ q (hq : q + 1 < k),
      (G.Reachable (outer ⟨3 * q + 1, by omega⟩)
          (middle ⟨3 * q + 1, by omega⟩) ∧
        G.Adj (middle ⟨3 * q + 1, by omega⟩)
          (middle ⟨3 * q + 2, by omega⟩)) ∨
      (G.Reachable (outer ⟨3 * (q + 1), by omega⟩)
          (middle ⟨3 * (q + 1), by omega⟩) ∧
        G.Adj (middle ⟨3 * q + 2, by omega⟩)
          (middle ⟨3 * (q + 1), by omega⟩))) :
    ∀ d, ∃ c, G.Reachable (outer c) (middle d) := by
  intro d
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
    · exact ⟨_, h⟩
    · exact ⟨_, h.trans (hpair q hq).2.symm.reachable⟩
  · have hq : q < k := by omega
    have hd' : d = ⟨3 * q + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [hd']
    rcases (hpair q hq).1 with h | h
    · exact ⟨_, h.trans (hpair q hq).2.reachable⟩
    · exact ⟨_, h⟩
  · have hq : q + 1 < k := by omega
    have hd' : d = ⟨3 * q + 2, by omega⟩ := Fin.ext (by simp; omega)
    rw [hd']
    rcases hgap q hq with h | h
    · exact ⟨_, h.1.trans h.2.reachable⟩
    · exact ⟨_, h.1.trans h.2.symm.reachable⟩

/-- The direct fields are already supplied by the right-slab and bridge
modules; only the two local attachment families remain. -/
theorem betterPersistentResidueZeroStepGeometry_of_attachments
    (k : Nat) (hk : 7 ≤ k)
    (htop : ∀ (r c : Fin (3 * (k + 1) - 1)),
      (r.val = 1 ∨ r.val = 2) → AttachesToWidenedOldInterior k hk (r, c))
    (happended : ∀ c : Fin (3 * (k + 1) - 1),
      AttachesToWidenedOldInterior k hk (⟨3 * k, by omega⟩, c)) :
    BetterPersistentResidueZeroStepGeometry k hk where
  topRows := htop
  rightSlab := persistentResidueZeroStepGeometry_rightSlab k hk
  appendedRow := happended
  anchorBridge := persistentResidueZeroStepGeometry_anchorBridge k hk

/-!
Applying the pointwise ladders leaves a distinguished boundary at the missing
pivot of `S_(k-2)`: the two rows at the two faces adjacent to that pivot.  The
structure below keeps those four goals separate from the uniform off-pivot
ladder, instead of hiding either part in a global connectedness premise.
-/

/-- Exact local top attachment boundary left by the `R_(k-2), S_(k-2),
R_(k-3)` ladders. -/
structure ResidueZeroTopLocalAttachmentGaps (k : Nat) (hk : 7 ≤ k) : Prop where
  offPivot :
    ∀ (r c : Fin (3 * (k + 1) - 1)),
      (r.val = 1 ∨ r.val = 2) →
      c.val ≠ 3 * (k - 2) → c.val ≠ 3 * (k - 2) + 1 →
      AttachesToWidenedOldInterior k hk (r, c)
  rowOneLeft : AttachesToWidenedOldInterior k hk
    (⟨1, by omega⟩, ⟨3 * (k - 2), by omega⟩)
  rowOneRight : AttachesToWidenedOldInterior k hk
    (⟨1, by omega⟩, ⟨3 * (k - 2) + 1, by omega⟩)
  rowTwoLeft : AttachesToWidenedOldInterior k hk
    (⟨2, by omega⟩, ⟨3 * (k - 2), by omega⟩)
  rowTwoRight : AttachesToWidenedOldInterior k hk
    (⟨2, by omega⟩, ⟨3 * (k - 2) + 1, by omega⟩)

/-- Filling exactly the four pivot gaps completes the top attachment field. -/
theorem ResidueZeroTopLocalAttachmentGaps.topRows
    {k : Nat} {hk : 7 ≤ k} (h : ResidueZeroTopLocalAttachmentGaps k hk) :
    ∀ (r c : Fin (3 * (k + 1) - 1)),
      (r.val = 1 ∨ r.val = 2) → AttachesToWidenedOldInterior k hk (r, c) := by
  intro r c hr
  by_cases hleft : c.val = 3 * (k - 2)
  · rcases hr with hr | hr
    · convert h.rowOneLeft using 1
      apply Prod.ext
      · exact Fin.ext hr
      · exact Fin.ext hleft
    · convert h.rowTwoLeft using 1
      apply Prod.ext
      · exact Fin.ext hr
      · exact Fin.ext hleft
  by_cases hright : c.val = 3 * (k - 2) + 1
  · rcases hr with hr | hr
    · convert h.rowOneRight using 1
      apply Prod.ext
      · exact Fin.ext hr
      · exact Fin.ext hright
    · convert h.rowTwoRight using 1
      apply Prod.ext
      · exact Fin.ext hr
      · exact Fin.ext hright
  exact h.offPivot r c hr hleft hright

/-- The exact attachment work still needed after the imported right slab and
anchor bridge: the symbolic top ladder (with its four pivot boundary cases)
and the `R_(k-1), R_k` appended-row ladder. -/
structure ResidueZeroLocalAttachmentGaps (k : Nat) (hk : 7 ≤ k) : Prop where
  top : ResidueZeroTopLocalAttachmentGaps k hk
  appended : ∀ c : Fin (3 * (k + 1) - 1),
    AttachesToWidenedOldInterior k hk (⟨3 * k, by omega⟩, c)

/-- Discharging exactly the local attachment package combines with the already
proved slab and bridge to give the improved successor geometry. -/
theorem ResidueZeroLocalAttachmentGaps.toBetterGeometry
    {k : Nat} {hk : 7 ≤ k} (h : ResidueZeroLocalAttachmentGaps k hk) :
    BetterPersistentResidueZeroStepGeometry k hk :=
  betterPersistentResidueZeroStepGeometry_of_attachments k hk h.top.topRows
    h.appended

/-- Conditional induction using precisely the improved geometry. -/
theorem persistentResidueZeroCertificate_of_betterGeometry
    (hgeom : ∀ k (hk : 7 ≤ k), BetterPersistentResidueZeroStepGeometry k hk)
    (k : Nat) (hk : 7 ≤ k) : PersistentResidueZeroCertificate k hk := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simpa using persistentResidueZeroCertificate_seven
  | succ d ih =>
      simpa [Nat.add_assoc] using
        PersistentResidueZeroCertificate.succ_of_betterGeometry (ih (by omega))
          (hgeom (7 + d) (by omega))

/-- Connectivity follows from any completed family of improved successor
geometries. -/
theorem uuDualGraph_uResidueZero_connected_of_betterGeometry
    (hgeom : ∀ k (hk : 7 ≤ k), BetterPersistentResidueZeroStepGeometry k hk)
    (k : Nat) (hk : 7 ≤ k) :
    (uuDualGraph (uResidueZero k hk)).Connected := by
  apply uuDualGraph_uResidueZero_connected_of_anchored k hk
  exact (persistentResidueZeroCertificate_of_betterGeometry hgeom k hk).toAnchored

/-- The target lower bound follows from the same improved local geometry. -/
theorem residueZero_le_maxPreserved_of_betterGeometry
    (hgeom : ∀ k (hk : 7 ≤ k), BetterPersistentResidueZeroStepGeometry k hk)
    (k : Nat) (hk : 7 ≤ k) :
    3 * k ^ 2 + 3 * k - 2 ≤ maxPreserved (3 * k) (3 * k) :=
  residueZero_le_maxPreserved_of_persistent k hk
    (persistentResidueZeroCertificate_of_betterGeometry hgeom k hk)

end GridGraphs
