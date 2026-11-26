import GridGraphs.ResidueTwoUpper.OneGap.FanPortTiny
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
/-- Sizes in `test` count plaquettes; arrival depths count tile rows. -/
theorem short_test : test 7 19 6 13 6 true := by native_decide
theorem medium_test : test 10 26 9 20 7 true := by native_decide
theorem long_test : test 13 33 12 27 9 true := by native_decide
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
