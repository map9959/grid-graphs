import GridGraphs.Accounting.BoundaryFive.SingletonBound
import GridGraphs.Accounting.BoundaryFive.Rootless.Reciprocal
import GridGraphs.Accounting.BoundaryFive.Rootless.CornerRoots

/-!
# The boundary-five c=2 endpoint: completed exclusion

Sources read: analysis/BOUNDARY_FIVE_PEELING.md and docs/PAPER_UPPER_PROGRAM.md,
as well as BoundaryFive/{Perimeter,TopSingleton,SingletonBound,Symmetry}.lean.
Coordinates in this discussion are zero-based. T=3k^2+7k, n=3k+2,
m=n-4=3k-2, e=(2k+1)/3. The profile under discussion is k>=5, k%3=1,
f=T+e, r=k+4, c=2, b=5. It is not the old k%3=2 connected endpoint.

## Checked results in this directory

* The singleton cap below uses actual ambient carriers and gives f<=T+2.
* Geometry proves domination from BoundaryRooted, the unique neighbor root
  at a U corner, horizontal interval extraction for a left/right boundary
  root, the strict m-1 cap, the m-3 covered-destination cap, and the m-2
  reciprocal-pair cap. These are actual grid statements, not length models.
* Reciprocal counts ALL actual induced components and proves
      f_D + m <= (m-1) q.
  At q=k this excludes even f_D+(12k-1)>=T, for k>=2. The theorem is written
  for left/right roots in one row. The transposed orientation is its paper
  symmetry consequence, not an additional checked transport theorem here.
* The no-reciprocal four-arrow classification is checked by ordinary decide.
* current_rooted_deep_endpoint_false in CornerRoots.lean now excludes the
  ENTIRE actual deep-rooted endpoint, including cyclic
  orientations. Its only hypotheses are the deep forest, one boundary root
  per forced component, four U corners, q=k, and the endpoint score.
* boundary_five_two_component_endpoint_false in AmbientEndpoint.lean excludes
  the actual ambient profile (r,c,b)=(k+4,2,5), with no gap-position or deep
  hypotheses. Import AmbientEndpoint for this result; this singleton module
  remains an earlier dependency of that theorem.

## Ambient reduction: checked in AmbientEndpoint

CornerPacket.Transport positions only the unique gap at (0,1)--(0,2),
preserving the actual cardinality and r,c,b. Other corner-hole choices stay
free. No canonical-frame construction or general perimeter-run count is used.

GapRoot proves that z=(2,2) in F would be a nonpure singleton, using the
actual perimeter path without c=1. The cap below contradicts that singleton.
Thus z is U; the all-U next ring then makes w=(1,2) an ambient isolate.

PeelingGraphs proves that at most two components plus an isolate makes all
other vertices connected. AnnulusPeeling obtains the same connectivity inside
the annulus from its cubic budget and its isolated w. DeepRooting then uses
the unique crossing edge between connected disjoint forest shores to exclude
two outward spokes at a deep F corner and two distinct roots in one deep
component. First exit of a full-graph path gives BoundaryRooted, including
putative deep isolates. The deep graph need not be connected.

DeepCrop supplies the exact coordinate isomorphism and f_D=f-(4n-9).
RootedLedger identifies forced components with boundary F roots, cancelling
their count from the grid ledger to give 3f_D+q=m^2. The endpoint mass now
gives q=k directly, avoiding a separate induced-component partition proof.

## Long-rod closure: checked, including the cyclic case

CornerRoots transports the covered-destination cap through all eight square
charts and obtains four DISTINCT actual corner-root carriers of length <=m-3.
The charts orient one root at a time and never fix another corner's choice.
RodInventory extracts the complete interval of every actual induced component.

Let DeltaStrict=k(m-1)-f_D=(4k-4)/3. For any carrier, at least three OTHER
corner carriers contribute two strict-deficit units each. Thus every carrier
has length >=(5k+13)/3>(m+1)/2. All intervals contain the same two central
positions; parallel axes are three-spaced by the four- and six-cycle obstructions.
Boundary-root uniqueness forces every nontrivial carrier axis into the interior.
At most two of the four corner carriers have either orientation, so H,V>=2.

For each perpendicular pair, one rod misses the entire triple centered on
the other's axis. Otherwise two preserved vertices meet, are adjacent, or
are diagonal cell corners. MissingTriples charges this triple to exactly one
recipient, with an explicit tie-break. Slots are labelled by the recipient
rod, and opposite-axis three-spacing prevents reuse within that recipient.
Consequently
  3HV <= DeltaFull = mk-f_D = (7k-4)/3.
But HV>=2(k-2), giving 6k-12<=(7k-4)/3, impossible for k>=7.
This closes the deep problem without a reciprocal/cyclic split or recursive
central-coverage packet. Additional boundary roots remain allowed.

The stated ambient profile is excluded. This does not by itself exclude
other endpoint profiles or improve the global bound. Neither c=1 nor
normalization of the other holes is assumed.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

/-- At r=k+4 an actual nonpure singleton forces f<=T+2, independently of c. -/
theorem singleton_card_le_stable_add_two {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4)
    (Z : ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent)
    (hZ : Z ∉ pureBoundaryCarriers F) (hsize : Z.supp.toFinset.card = 1) :
    F.card ≤ 3 * k ^ 2 + 7 * k + 2 := by
  have h := card_add_side_le_of_singleton (by omega) F hacyc hb Z hZ hsize
  rw [hr] at h
  have hm : 3 * k + 2 - 4 + 2 = 3 * k := by omega
  nlinarith

/-- No singleton at the current endpoint in the r=k+4,b=5 profile.
The c=2 condition is not needed for this particular obstruction. -/
theorem current_endpoint_no_nonpure_singleton {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card)
    (Z : ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent)
    (hZ : Z ∉ pureBoundaryCarriers F) : Z.supp.toFinset.card ≠ 1 := by
  intro hsize
  have h := singleton_card_le_stable_add_two hk F hacyc hb hr Z hZ hsize
  have he : 5 ≤ (2 * k + 1) / 3 := by omega
  omega

end GridGraphs.BoundaryFive.Rootless
