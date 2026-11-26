import GridGraphs.NoPitch.FaceJoinRank
import GridGraphs.NoPitch.Certificate
import GridGraphs.NoPitch.StarCoverage

namespace GridGraphs.NoPitch.FaceJoin
open GridGraphs.NoPitch.Dual PitchCut

/-- The chart convention is an eightfold integer physical vector and
twice the RHS. An upper estimate of the decoded left-hand side by the
physical difference suffices; equality of the two is not required. -/
theorem decoded_of_translation {k} (F : Finset (Site k)) (acy : (Budget.G F).IsAcyclic)
    (D : Chart) (i : Fin D.rows.size) (t : Int)
    (sense : D.rows[i].sense=1) (rhs : D.rows[i].rhs.atStep t=0)
    (translation : lhs D (physicalVector D F (Budget.out F)) i ≤
      8*((total F:Int)-(Budget.exits F).card)) :
    rowHolds D.rows[i].sense (2*lhs D (physicalVector D F (Budget.out F)) i)
      (8*D.rows[i].rhs.atStep t) := by
  have le : (total F:Int) ≤ (Budget.exits F).card := by exact_mod_cast total_le_exits F acy
  rw [sense,rhs]
  change 2*lhs D (physicalVector D F (Budget.out F)) i ≤ 8*0
  linarith

/-- The exported duals retain nonzero multipliers only. Scan their
actual term lists for a zero-RHS ≤ row supported on both a face
(key tag 2) and a star (tag 0 or 1). This does not read any prices. -/
def mixedJoinCandidate (D : Chart) : Bool := Id.run do
  let mut seen := Array.replicate D.rows.size (0 : Nat)
  for c in D.cols do
    let tag := c.key%8
    if tag≤2 then
      for (i,w) in c.terms do
        if w≠0 then
          seen := seen.modify i (fun a => a ||| (if tag=2 then 2 else 1))
  return (List.range D.rows.size).any fun i =>
    let r := D.rows[i]!
    seen[i]! == 3 && r.sense == 1 && r.rhs == ⟨0,0,0⟩

theorem no_retained_mixed_join_candidate :
    [chart19,chart22,chart25,chart52,chart58,chart61].all (fun D => !mixedJoinCandidate D) := by
  native_decide

end GridGraphs.NoPitch.FaceJoin
