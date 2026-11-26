import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayCache

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan

-- The candidate schedule has both orientations, and uses no depth-three strips.
example : (stripSchedule 14 4 0).length=100 := by native_decide

-- Exercise the executable stopping test in both directions.
example : cachedExecute (stripSchedule 14 1 0) (fun _ _ => [])=true := by native_decide
example : cachedExecute ([] : List (Update 14)) (initialBank 14)=false := by native_decide

-- No domain starts empty. A single strip must delete all-mark words:
-- adjacent all-mark site-lines force a cycle.
example : cachedExecute ((stripSchedule 14 1 0).take 1)
    (fun _ _ => [(511,511,511,511)])=true := by native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
