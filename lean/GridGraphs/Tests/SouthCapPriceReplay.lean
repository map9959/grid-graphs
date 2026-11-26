import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPriceClauses

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil Std.Sat

/-- Decode the `(significance mask, value)` pairs used by
`tight_corner_sat.cover`. The wire order is the producer's bit order. -/
def unpackCube {n : Nat} (order : List (Fin n)) (m b : Nat) : Cube n :=
  (order.zipIdx.filter fun (_,j) => m.testBit j).map fun (i,j) => (i,b.testBit j)

-- External producer: table(119).patch at the representative for tag
-- (10,12), at the origin of the 6×6 projection.
def probePatch : List (Nat × Nat) :=
  [(17,17),(10,10),(34,34),(20,20),(136,136),(80,80),(272,272),(160,160),(135,133),
   (195,195),(323,323),(45,45),(269,269),(101,101),(325,325),(389,389),(105,97),
   (353,353),(326,326),(390,390),(450,322),(300,268),(332,332),(360,360),(47,5),
   (203,65),(422,260),(488,320),(427,1),(427,256),(238,4),(238,64),(191,0)]

theorem probe_patch_checked :
    ∀ mb ∈ probePatch, badCube (unpackCube (List.finRange 9) mb.1 mb.2)
      (fun a => maskOK (mask9 a)) (patchPrice (106,112)) := by native_decide

/-- All 33 emitted clauses hold on any assignment with the actual
physical patch's price and admissibility. -/
theorem probe_patch_rows {V : Type} (W : WindowField V) (slot : Fin 9 → V)
    (ok : maskOK (mask9 fun i => W.mark (slot i)))
    (zero : patchPrice (106,112) (fun i => W.mark (slot i))=0) :
    Holds W (probePatch.map fun (m,b) =>
      priceRow [] (cubeLits (Wire.mark ∘ slot) (unpackCube (List.finRange 9) m b))) := by
  intro c mem
  obtain ⟨⟨m,b⟩,h,rfl⟩ := List.mem_map.mp mem
  exact atlas_patch_clause W slot _ _ (probe_patch_checked _ h) ok zero

-- The producer omits the off-board south neighbour of (118,117).
-- Map its four-bit words into the Lean order (centre, east, south,
-- west, north). This is the non-sink row for each possible exit.
def probeStar : List (Nat × List (Nat × Nat)) :=
  [(0,[(3,0),(9,8),(10,10),(12,12),(7,3),(13,1)]),
   (2,[(2,0),(4,0),(8,8)]),
   (3,[(1,1),(2,2),(4,4),(8,0)])]
def clippedStarOK (out : Nat) (a : Fin 5 → Bool) :=
  !a 2 && starOK 119 (118,117) (a 0).toNat (code fun i : Fin 4 => a i.succ) out

theorem probe_star_checked : ∀ row∈probeStar, ∀ mb∈row.2,
    badCube (unpackCube [0,1,3,4] mb.1 mb.2)
      (clippedStarOK row.1) (starPrice (118,117) row.1) := by native_decide

theorem probe_star_rows {V : Type} (W : WindowField V) (sample : Fin 5 → Wire V)
    (row : Nat × List (Nat × Nat)) (mem : row∈probeStar)
    (guard : CNF.Clause (Wire V))
    (clean : guard.eval (value W)≠true →
      clippedStarOK row.1 (value W ∘ sample)=true ∧
      starPrice (118,117) row.1 (value W ∘ sample)=0) :
    Holds W (row.2.map fun (m,b) =>
      priceRow guard (cubeLits sample (unpackCube [0,1,3,4] m b))) := by
  intro c h
  obtain ⟨⟨m,b⟩,mb,rfl⟩ := List.mem_map.mp h
  exact finite_price_row W _ _ _ _ _ (probe_star_checked row mem _ mb) clean

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
