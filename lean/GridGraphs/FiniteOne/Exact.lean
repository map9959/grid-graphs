import GridGraphs.FiniteOne.Sound

namespace GridGraphs.FiniteOne

private theorem finish (k b : Nat) (t : Prices) (hn : 2≤3*k+1)
    (score : squareScore (3*k+1)=b) (check : budget t (3*k+1)<(t.unit:Int)*(b+1:Nat)) :
    maxPreserved (3*k+1) (3*k+1)=b :=
  Nat.le_antisymm (upper hn t check) (score ▸ squareScore_lower_residue_one k)

private def t16 := decode 16 (include_str "Data/s16.v32")
private def t28 := decode 28 (include_str "Data/s28.v32")
private def t31 := decode 31 (include_str "Data/s31.v32")
private def t34 := decode 34 (include_str "Data/s34.v32")
private def t37 := decode 37 (include_str "Data/s37.v32")
private def t40 := decode 40 (include_str "Data/s40.v32")
private def t46 := decode 46 (include_str "Data/s46.v32")
private def t49 := decode 49 (include_str "Data/s49.v32")
private def t55 := decode 55 (include_str "Data/s55.v32")

theorem exact16 : maxPreserved 16 16=100 := finish 5 100 t16 (by decide) (by decide) (by native_decide)
theorem exact28 : maxPreserved 28 28=289 := finish 9 289 t28 (by decide) (by decide) (by native_decide)
theorem exact31 : maxPreserved 31 31=351 := finish 10 351 t31 (by decide) (by decide) (by native_decide)
theorem exact34 : maxPreserved 34 34=420 := finish 11 420 t34 (by decide) (by decide) (by native_decide)
theorem exact37 : maxPreserved 37 37=494 := finish 12 494 t37 (by decide) (by decide) (by native_decide)
theorem exact40 : maxPreserved 40 40=574 := finish 13 574 t40 (by decide) (by decide) (by native_decide)
theorem exact46 : maxPreserved 46 46=753 := finish 15 753 t46 (by decide) (by decide) (by native_decide)
theorem exact49 : maxPreserved 49 49=851 := finish 16 851 t49 (by decide) (by decide) (by native_decide)
theorem exact55 : maxPreserved 55 55=1066 := finish 18 1066 t55 (by decide) (by decide) (by native_decide)

end GridGraphs.FiniteOne
