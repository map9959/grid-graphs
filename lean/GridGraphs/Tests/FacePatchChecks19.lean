import GridGraphs.NoPitch.CachedFaceReplay19
import GridGraphs.NoPitch.Certificate

namespace GridGraphs.NoPitch.FaceRows
open GridGraphs.NoPitch.Dual

theorem other19 : otherOK chart19 := by native_decide
theorem rows19 : rowOK chart19 := by native_decide
theorem unused19 : unusedOK chart19 := CachedReplay.unused_sound chart19 (by native_decide)
theorem tiles19 : tileOK chart19 := CachedReplay.patch_sound chart19 (by native_decide)

end GridGraphs.NoPitch.FaceRows
