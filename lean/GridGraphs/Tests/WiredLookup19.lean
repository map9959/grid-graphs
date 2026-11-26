import GridGraphs.NoPitch.WiredFace
import GridGraphs.NoPitch.Certificate

namespace GridGraphs.NoPitch.Wired
open Keys

theorem mask_roundtrip : ∀ m : Mask, rotatedMask m 0<65536 ∧ maskOf (rotatedMask m 0)=m := by
  native_decide

def eqRel (q : PartitionBits) := ∀ i j l, q i i=true ∧ q i j=q j i ∧ (q i j → q j l → q i l)
instance (q : PartitionBits) : Decidable (eqRel q) := by unfold eqRel; infer_instance

theorem partition_roundtrip : ∀ q : PartitionBits, eqRel q →
    colorCode q∈partitions ∧ partOf (colorCode q)=q := by native_decide

theorem lookup19 : lookupAll Dual.chart19 6 = true := by native_decide

end GridGraphs.NoPitch.Wired
