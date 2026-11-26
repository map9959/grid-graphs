import GridGraphs.NoPitch.CachedFaceReplay19
import GridGraphs.NoPitch.Certificate

namespace GridGraphs.NoPitch.FaceLines
open GridGraphs.NoPitch.Dual
theorem other19 : otherCheck chart19 := by native_decide
theorem meta19 : metaCheck chart19 := by native_decide
theorem keys19 : LineKeys.allKeys chart19 := by native_decide
theorem steps19 : stepCheck chart19 := CachedReplay.step_sound chart19 (by native_decide)
theorem tiles19 : tileCheck chart19 := CachedReplay.line_sound chart19 (by native_decide)
end GridGraphs.NoPitch.FaceLines
