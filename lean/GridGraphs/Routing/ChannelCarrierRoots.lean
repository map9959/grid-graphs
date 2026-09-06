import GridGraphs.Forests.PlaneChannelForest
import GridGraphs.Routing.NoncrossingShoreChannels

/-!
# Component carriers for channel-forest roots

This file isolates the root resource needed by a channel-forest pruning
argument.  A root contact is a vertex outside the cotree support.  Its resource
is the connected component of the induced graph containing that vertex.

The predicate `CarrierPruned` is deliberately the remaining geometric
obligation: distinct surviving roots must contact distinct components.  No
channel realization or final contour inequality is asserted here.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {V X : Type*}

/-- Vertices not occupied by a chosen cotree support. -/
def CotreeFreeSet [Fintype X] [DecidableEq X] (U : Finset X) : Finset X :=
  Finset.univ \ U

/-- The ambient graph induced by the vertices outside the cotree support. -/
def CotreeFreeGraph [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) (U : Finset X) : SimpleGraph ↥(CotreeFreeSet U) :=
  G.induce (↑(CotreeFreeSet U) : Set X)

namespace ParentForest

variable [Fintype V] [DecidableEq V] (F : ParentForest V)
variable [Fintype X] [DecidableEq X] (G : SimpleGraph X) (U : Finset X)

/-- Distinct surviving roots use distinct connected-component carriers.

The contact map is typed to ensure every root terminates outside `U`; this
predicate records only the additional component-level pruning obligation. -/
def CarrierPruned
    (rootContact : ↥F.roots → ↥(CotreeFreeSet U)) : Prop :=
  Function.Injective fun r =>
    (CotreeFreeGraph G U).connectedComponentMk (rootContact r)

/-- A carrier-pruned root contact map realizes the forest roots as distinct
components of the cotree-free induced graph. -/
def terminalRootComponentEmbedding
    (rootContact : ↥F.roots → ↥(CotreeFreeSet U))
    (hpruned : F.CarrierPruned G U rootContact) :
    ↥F.roots ↪ (CotreeFreeGraph G U).ConnectedComponent where
  toFun r := (CotreeFreeGraph G U).connectedComponentMk (rootContact r)
  inj' := hpruned

/-- Raw terminal occurrences are equivalent when their contacts lie in the
same cotree-free connected component. -/
def terminalCarrierSetoid
    (rootContact : ↥F.roots → ↥(CotreeFreeSet U)) : Setoid ↥F.roots :=
  Setoid.ker fun r =>
    (CotreeFreeGraph G U).connectedComponentMk (rootContact r)

/-- The canonical quotient of raw root occurrences by component carrier. -/
abbrev TerminalCarrierQuotient
    (rootContact : ↥F.roots → ↥(CotreeFreeSet U)) :=
  Quotient (F.terminalCarrierSetoid G U rootContact)

/-- The carrier quotient always embeds in the component resource, without a
`CarrierPruned` hypothesis. -/
def terminalCarrierQuotientEmbedding
    (rootContact : ↥F.roots → ↥(CotreeFreeSet U)) :
    F.TerminalCarrierQuotient G U rootContact ↪
      (CotreeFreeGraph G U).ConnectedComponent where
  toFun := Quotient.lift
    (fun r => (CotreeFreeGraph G U).connectedComponentMk (rootContact r))
    (fun _ _ h => h)
  inj' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro r s hrs
    exact Quotient.sound hrs

end ParentForest

end GridGraphs
