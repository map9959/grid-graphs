import GridGraphs.Geometry.CapStripAssembly
import GridGraphs.Geometry.CapPitchArrows
import GridGraphs.Tests.SlitCertificateReplay
import GridGraphs.Results.PitchUpper

namespace GridGraphs.CapSite

/-- This closed check compares all admissible five-bit windows and both
arrow masks (including final blank-row charges) against the actual tables
used by the width induction. No physical classification is postulated. -/
theorem tables_verified : tablesOK = true := by native_decide

theorem strip_trace_verified {k as} (hk : k<4) (physical : PhysicalStrip k initial as) :
    GridGraphs.Slit.Trace (trans k) 0 (stripCost initial as)
      (as.map (letter · 0)) (as.map (letter · 3)) ∧
    (stripCost initial as : Int) = stripGeom initial as-2+2*stripSinks initial as :=
  physical_strip_trace tables_verified hk physical

end GridGraphs.CapSite

namespace GridGraphs.PitchCut

/-- No computation, cap encoding or rank hypothesis in the statement. -/
theorem pitch_upper_verified {k : Nat} (F : Finset (Site k)) (v : Fin (N k))
    (hk : 5≤k) (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (pitch : Pitch F v ∨ Pitch (transpose F) v) : F.card ≤ squareScore (N k) :=
  acyclic_pitch_upper F v CapSite.tables_verified Slit.Replay.replay_verified hk acy pitch

theorem exact_of_no_pitch_verified {k : Nat} (hk : 5≤k)
    (noPitch : ∀ F : Finset (Site k), F ∈ acyclicForcedSets (N k) (N k) →
      F.card=maxPreserved (N k) (N k) →
      (∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) → F.card ≤ squareScore (N k)) :
    maxPreserved (N k) (N k) = squareScore (N k) :=
  exact_of_no_pitch CapSite.tables_verified Slit.Replay.replay_verified hk noPitch

end GridGraphs.PitchCut
