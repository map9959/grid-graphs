import GridGraphs.NoPitch.PhysicalWiring
import GridGraphs.Tests.WiredLookup19

namespace GridGraphs.NoPitch.Wired
open PitchCut Keys

theorem compatible_found {k} (D : Dual.Chart) (ok : lookupAll D k) (m : Mask) (q : PartitionBits) (eq : eqRel q)
    (raw : fresh initial (rawEdges m)) (h : compatible m q) (p : FacePos k) :
    (Dual.locate D (Dual.index D) (faceCode p m q)).isSome := by
  obtain ⟨lt,mask⟩ := mask_roundtrip m
  obtain ⟨mem,part⟩ := partition_roundtrip q eq
  unfold lookupAll at ok; simp only [decide_eq_true_eq] at ok
  have all := ok (⟨_,lt⟩ : Fin 65536)
  rw [mask] at all
  have yes : colorCode q∈catalog m := List.mem_filter.mpr ⟨mem,by rwa [part]⟩
  simpa only [faceCode,part] using all raw _ yes p

end GridGraphs.NoPitch.Wired

namespace GridGraphs.NoPitch.Wired
open PitchCut Keys

theorem physical_partition {k} (F : Finset (Site k)) (p : FacePos k) : eqRel (faceAtom F p).2 := by
  intro i j l
  simp only [faceAtom,joined,decide_eq_true_eq]
  refine ⟨.rfl,?_,fun a b => a.trans b⟩
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (SimpleGraph.reachable_comm (G:=G (skeleton F))
    (u:=corner p i) (v:=corner p j))

/-- In the free side-19 chart, dominance removed no wired-compatible
face. The physical theorem consequently needs neither optimality nor an
assumption about the line type. -/
theorem physical_face19 (F : Finset (Site 6)) (acy : (G F).IsAcyclic) (p : FacePos 6) :
    (Dual.locate Dual.chart19 (Dual.index Dual.chart19) (face F p)).isSome := by
  have wired := physical_wiring p F acy
  exact compatible_found _ lookup19 _ _ (physical_partition F p) wired.1 wired.2 p

end GridGraphs.NoPitch.Wired
