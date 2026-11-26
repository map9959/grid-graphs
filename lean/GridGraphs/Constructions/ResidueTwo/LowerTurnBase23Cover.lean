import GridGraphs.Constructions.ResidueTwo.LowerTurnRailTail

namespace GridGraphs.ResidueTwoLower.Poly

def input23 := (decode (include_str "LowerTurnData/base23.turns")).getD #[]

theorem cover23 : coverOK input23 (widthExpr 23) (ordinaryRegion 23) = true := by
  native_decide

theorem forced23 (t : Nat) (v : Turn.Pt) (d : Turn.Dir)
    (h : Turn.forced (23+42*t) (marks (23+42*t)) v d) : allowed input23 0 d t v :=
  cover_sound _ (fun i j => by simp [widthExpr,Exp.eval])
    (fun i j hi hj hm => ordinary_covers 23 t i j (.inl rfl) hi hj hm) cover23 v d h

end GridGraphs.ResidueTwoLower.Poly
