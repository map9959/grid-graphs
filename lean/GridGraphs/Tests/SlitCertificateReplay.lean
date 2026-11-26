import GridGraphs.Geometry.SlitWidthBound

/-! Standalone compiled replay. This module isolates the native evaluation
trust dependency from the graph and induction theorems. Regenerate the
finite tables with `python3 -B -m analysis.research_program.export_slit_lean`. -/
namespace GridGraphs.Slit.Replay

/-- The compiler is used *only* for the closed finite Boolean computation. -/
theorem replay_verified : replay requests = true := by native_decide

/-- All heights and widths, for the exported local transducer. -/
theorem cap_excludes_verified {n i j c d u v} (hn : 4≤n) (pos : 0 < i+j)
    (l : Prefix 2 i c u) (r : Prefix n j d v) (matched : Trace Data.reflect 0 0 u v) :
    maxBill (i+j) < (c : Int)+d :=
  cap_excludes replay_verified hn pos l r matched

end GridGraphs.Slit.Replay
