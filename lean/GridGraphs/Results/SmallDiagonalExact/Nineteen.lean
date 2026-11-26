import GridGraphs.NoPitch.Budget.AllNonFace19
import GridGraphs.Tests.PhysicalFaceRows19
import GridGraphs.Tests.PhysicalFaceLineRows19

namespace GridGraphs
open NoPitch
attribute [local irreducible] NoPitch.Dual.chart19

theorem maxPreserved_nineteen_nineteen : maxPreserved 19 19 = 138 :=
  LocalBoard19.exact19_of_face_rows
    (fun F h i hi => FaceRows.physical_patch_rows19 F h (Budget.out F) i hi)
    (fun F h np i hi => FaceLines.physical_face_line_rows19 F h np (Budget.out F) i hi)

end GridGraphs
