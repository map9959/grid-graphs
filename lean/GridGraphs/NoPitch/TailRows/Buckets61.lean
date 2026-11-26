import GridGraphs.NoPitch.TailRows.NormShape

namespace GridGraphs.NoPitch.TailRows
open Keys GridGraphs.NoPitch.Dual
def buckets61 : Array NormShape := #[
  ⟨61,8,[0,1,8,0],⟨0,0,1,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[2,2,9,0],⟨2,0,2,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[3,4,8,0],⟨3,0,4,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[4,9,0,4],⟨4,0,51,6,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[4,8,0,3],⟨4,0,50,6,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[4,8,2,0],⟨4,0,11,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[4,8,0,0],⟨4,0,14,0,0,1,0,12,2,0⟩,⟨24,4,0⟩⟩,
  ⟨61,8,[6,6,9,0],⟨6,0,6,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[6,9,0,6],⟨6,0,51,6,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[6,9,0,3],⟨6,0,48,6,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[6,9,0,0],⟨6,0,15,0,0,1,0,11,2,0⟩,⟨22,4,0⟩⟩,
  ⟨61,8,[7,7,9,0],⟨7,0,7,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[7,9,0,4],⟨7,0,48,6,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[9,9,0,9],⟨9,0,51,6,-3,6,1,1,0,0⟩,⟨12,2,0⟩⟩,
  ⟨61,8,[9,9,0,3],⟨9,0,45,6,-3,5,1,1,0,0⟩,⟨10,2,0⟩⟩,
  ⟨61,8,[9,9,0,0],⟨9,0,18,0,3,5,1,9,2,-2⟩,⟨50,20,2⟩⟩,
  ⟨61,8,[8,8,9,18],⟨35,3,35,3,3,6,1,1,0,0⟩,⟨12,2,0⟩⟩,
  ⟨61,8,[8,9,14,18],⟨38,3,33,3,3,5,1,1,0,0⟩,⟨10,2,0⟩⟩,
  ⟨61,8,[9,9,3,3],⟨24,3,30,3,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[8,9,14,14],⟨35,3,30,3,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[9,9,3,9],⟨27,3,33,3,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨61,8,[9,9,9,9],⟨30,3,30,3,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨59,7,[0,1,8,0],⟨0,0,1,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨59,7,[2,2,9,0],⟨2,0,2,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨59,7,[5,5,9,0],⟨5,0,5,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨59,7,[6,7,5,0],⟨6,0,10,0,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨59,7,[8,8,0,9],⟨8,0,50,6,-3,6,1,1,0,0⟩,⟨12,2,0⟩⟩,
  ⟨59,7,[7,7,0,13],⟨13,0,49,6,-3,5,1,1,0,0⟩,⟨10,2,0⟩⟩,
  ⟨59,7,[7,7,3,13],⟨28,3,34,3,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩,
  ⟨59,7,[8,8,3,9],⟨26,3,32,3,0,1,0,1,0,0⟩,⟨2,0,0⟩⟩]
private theorem valid_61_0 : (buckets61[0]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_1 : (buckets61[1]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_2 : (buckets61[2]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_3 : (buckets61[3]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_4 : (buckets61[4]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_5 : (buckets61[5]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_6 : (buckets61[6]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_7 : (buckets61[7]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_8 : (buckets61[8]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_9 : (buckets61[9]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_10 : (buckets61[10]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_11 : (buckets61[11]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_12 : (buckets61[12]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_13 : (buckets61[13]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_14 : (buckets61[14]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_15 : (buckets61[15]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_16 : (buckets61[16]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_17 : (buckets61[17]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_18 : (buckets61[18]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_19 : (buckets61[19]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_20 : (buckets61[20]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_21 : (buckets61[21]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_22 : (buckets61[22]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_23 : (buckets61[23]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_24 : (buckets61[24]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_25 : (buckets61[25]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_26 : (buckets61[26]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_27 : (buckets61[27]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_28 : (buckets61[28]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip
private theorem valid_61_29 : (buckets61[29]!).Valid := by
  dsimp [buckets61,NormShape.Valid]; verify_strip

theorem shapes61 (j : Fin 30) : (buckets61[j.val]!).Valid := by
  fin_cases j
  exacts [valid_61_0,valid_61_1,valid_61_2,valid_61_3,valid_61_4,valid_61_5,valid_61_6,valid_61_7,valid_61_8,valid_61_9,valid_61_10,valid_61_11,valid_61_12,valid_61_13,valid_61_14,valid_61_15,valid_61_16,valid_61_17,valid_61_18,valid_61_19,valid_61_20,valid_61_21,valid_61_22,valid_61_23,valid_61_24,valid_61_25,valid_61_26,valid_61_27,valid_61_28,valid_61_29]

end GridGraphs.NoPitch.TailRows
