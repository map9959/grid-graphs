import GridGraphs.ResidueTwoUpper.OneGap.SouthCapWords

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap

def packWord (w : Word) := w.1+512*(w.2.1+512*(w.2.2.1+512*w.2.2.2))

/-- The ordinary catalogue uses six printable bytes per 36-bit word.
Each line is one tag pair; only tags 6–12 occur in the southern crop. -/
def decodeBank (s : String) : Array (Array Nat) :=
  ((s.splitOn "\n").filter (!·.isEmpty)).toArray.map fun line => Id.run do
    let b := line.toUTF8
    let mut out := #[]
    for j in [:b.size/6] do
      let mut v := 0
      for i in [:6] do v := v + ((b[6*j+i]!.toNat-48) <<< (6*i))
      out := out.push v
    return out

private def bankText := include_str "SouthCapBank.txt"
def packedBank := decodeBank bankText
def ordinary (r c : Nat) (w : Word) : Prop :=
  6≤r ∧ r≤12 ∧ 6≤c ∧ c≤12 ∧
  (packedBank[7*(r-6)+(c-6)]?).any (·.contains (packWord w))

theorem packed_bank_size :
    packedBank.size=49 ∧ (packedBank.map Array.size).toList.sum=14555 := by native_decide

theorem packed_bank_bytes : bankText.toUTF8.size=87379 := by native_decide

/-- These are two of the concrete missing local words. This check
asserts nonmembership in the saved bank, not physical realizability. -/
theorem closed_word_delta :
    ¬ordinary 10 11 (292,128,292,32) ∧ ¬ordinary 10 12 (192,24,32,24) ∧
    widened ordinary 10 11 (292,128,292,32) ∧ widened ordinary 10 12 (192,24,32,24) := by
  unfold widened ordinary
  native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
