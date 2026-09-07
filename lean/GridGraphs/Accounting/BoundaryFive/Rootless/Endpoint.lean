import GridGraphs.Accounting.BoundaryFive.SingletonBound
import GridGraphs.Accounting.BoundaryFive.Rootless.Reciprocal

/-!
# The remaining c=2 endpoint: scope and open gate

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

## Ambient reduction: paper argument, NOT a theorem supplied here

Position only the unique perimeter gap at (0,1)--(0,2). Leave the other
three corner-hole choices free. The all-U next ring and forced perimeter
path give a tree on the outer two rings except w=(1,2). The corner-neighbor
hole on every other corner leaves one spoke, not two missing spokes at that
next-ring corner. Thus w is the sole exception for every such choice.

Put z=(2,2). If z is F, the off-boundary path argument in TopSingleton
excludes its two deep F neighbors without needing ambient c=1: connectivity
in that proof was used to obtain z in F, not for the path contradiction.
Its other neighbors are next-ring U. Hence z would be a nonpure singleton,
contradicting the checked cap below. Thus z is U, and w is isolated.

Since c=2 on ALL vertices, the other component contains every vertex other
than w. An ordinary deep F corner would have two attachments to the same
outer tree, closing a cycle. Consequently all four deep corners are U.
Every deep forced component must have an attachment to the outer tree, so
has a boundary F root. Two distinct such roots in one deep component would
give a second path between their attachments and close a cycle. Therefore
BoundaryRooted and UniqueBoundaryRoots hold in the deep square. In
particular it is fully dominated, although it need not be connected.

The four perimeter F runs are separated from the deep square by the all-U
next ring, so q=r-4=k and f_D=f-(4n-9)=3k^2-5k+1+e. These deductions still
need an ambient-to-deep Lean bridge; the canonical construction's iff is
not silently applied to a differently oriented set of corner holes.

## Precise cyclic gate

Each U corner has exactly one adjacent boundary F root. Its induced carrier
is perpendicular to that boundary side (or a singleton), and points toward
the adjacent corner. The four roots, and hence their carriers, are distinct.
A reciprocal pair is exactly the collinear opposite-boundary situation
handled above. Without one, the checked four-arrow lemma leaves only a
directed cycle and its reverse. A square symmetry changes one to the other.

In the clockwise representative the four F roots are
  (1,0), (0,m-2), (m-2,m-1), (m-1,1).
The four deep corners are U. The exact unresolved class consists of an
acyclic deep F with BoundaryRooted, UniqueBoundaryRoots, q=k, these four
roots, and f_D=3k^2-5k+1+(2k+1)/3. Additional boundary roots are allowed;
neither four forced components nor four total boundary roots is assumed.

Let Delta=k(m-1)-f_D. At the endpoint Delta=(4k-4)/3, so exclusion requires
Delta >= (4k-1)/3. The four m-3 corner-root caps alone give Delta>=8.
Thus a cyclic proof still needs an additional (4k-25)/3 units beyond those
eight, using actual central coverage/attachments or another incompatibility.
For the first admissible k=7 this is one additional unit; it is not zero.
The reciprocal pair's loss is m already, not eight independent charges
added on top of that pair's full loss. No central-coverage packet inequality
or cyclic infeasibility certificate has been proved in this directory.

There is no unconditional exclusion of the ambient profile here. In
particular neither c=1 nor normalization of the other holes is assumed.
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
