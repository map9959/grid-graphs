import GridGraphs.ResidueTwoUpper.OneGap.FanPortSpeed

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port

/-- Only three extra local exclusions are needed for the rooted move. -/
def banned := [(9,258,73,16),(129,288,9,2),(73,16,73,129)]
def repaired := poolWith (fun a b c d => markOK a b c d && !banned.contains (a,b,c,d)) (shapes.map fun m => (m,labels m))
theorem root_test : testWith repaired 9 9 3 4 5 false := by native_decide
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
