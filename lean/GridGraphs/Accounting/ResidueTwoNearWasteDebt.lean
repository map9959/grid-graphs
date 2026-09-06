import GridGraphs.Accounting.ResidueTwoNearWasteStructure
import GridGraphs.Results.DiagonalUpperResidue

/-!
# The remaining stable residue-two debt obligation

The proposition below is the semantic endpoint of the missing arbitrary-width
silent-hull argument.  A proof must cover silent carrier passages and propagate
OUT-rooted attachment debt through every phase; finite-width transition censuses
do not prove it.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- Minimal width-independent persistent-attachment-debt statement: an old
baseline support in the stable residue-two range has one more unit of four-side
component charge than the near-waste identity permits. -/
def StableResidueTwoPersistentAttachmentDebt : Prop :=
  ∀ (k : Nat), 5 ≤ k →
    ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
      (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T)).card =
        6 * k ^ 2 + 5 * k + 3 →
      3 * k + 10 ≤ fourSideComponentRank (3 * k + 2)
        (supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T))

/-- The persistent debt theorem is exactly sufficient to exclude stable
near-waste equality. -/
theorem StableResidueTwoNearWasteExcluded_of_persistentAttachmentDebt
    (hdebt : StableResidueTwoPersistentAttachmentDebt) :
    StableResidueTwoNearWasteExcluded := by
  intro k hk T _ hT hnear
  have hcard := residueTwo_nearWaste_support_card hT hnear
  have hgap := hdebt k hk T hT hcard
  have hexact := residueTwo_nearWaste_fourSide_identity hT hnear
  omega

end GridGraphs
