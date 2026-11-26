import GridGraphs.ResidueTwoUpper.OneGap.FanSouthHandoff
import GridGraphs.ResidueTwoUpper.OneGap.FanSouthCollision

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
#print axioms FanBoot.front_of_score
#print axioms FanBoot.physical_dangling_step
#print axioms FanBoot.physical_root_step
#print axioms FanBoot.last_line_cap
#print axioms Speed.schedule_iff
#print axioms FanBoot.CollisionWide.plateau17
#print axioms FanBoot.south_handoff_with_collision_of_score
#print axioms FanBoot.south_handoff_of_score

-- The open-bulk stripe in OneGapBulkObstruction is not a speed-window tile.
example : 7 ∉ FanBoot.Port.shapes := by decide
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
