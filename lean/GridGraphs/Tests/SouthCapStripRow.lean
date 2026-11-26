import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripTrace

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.Row

private def tiny (wired : Bool) : Program 2 :=
  ⟨fun j i => j==0 && i==0,fun j i => wired && j==0 && i==0,fun _ _ => false⟩

-- First row: both sites are in the apex component with representative 0.
example : (tiny true).run (basePartition 2).pack 1 = some ⟨0,1,1⟩ := by decide

-- Second row: slot 1 becomes a singleton; the old mark survives as a
-- component flag at slot 0, although neither new site is marked.
example : (tiny true).run (basePartition 2).pack 2 = some ⟨16,1,1⟩ := by decide

-- Without the wire, the marked component is rejected on disappearance.
example : (tiny false).run (basePartition 2).pack 3 = none := by decide

-- With the wire the old mark is still recorded at the apex after
-- the other slots are forgotten.
example : (tiny true).run (basePartition 2).pack 3 = some ⟨528,4,4⟩ := by decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.Row
