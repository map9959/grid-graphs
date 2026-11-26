import GridGraphs.Geometry.SlitWidthBound
import GridGraphs.Geometry.PitchCutRank
import GridGraphs.Geometry.PitchSkeletonPrice

namespace GridGraphs.PitchCut
open GridGraphs.Slit GridGraphs.Slit.Data GridGraphs.Slit.Replay
open SimpleGraph

/-- Data still to be extracted from the marked physical cap. No rank
price or bound on the bonus is assumed here. Both prefix words must
arise at the same height and match after reflection. -/
structure CapTrace (k rank : Nat) (bonus : Int) where
  leftKept : Nat
  rightKept : Nat
  leftBill : Nat
  rightBill : Nat
  leftWord : List Nat
  rightWord : List Nat
  kept : leftKept+rightKept+rank = k+1
  pos : 0 < leftKept+rightKept
  bill : 4*bonus = 2*((k:ℤ)+1)+2*rank-leftBill-rightBill
  leftTrace : Prefix 2 leftKept leftBill leftWord
  rightTrace : Prefix (k-1) rightKept rightBill rightWord
  seam : Trace reflect 0 0 leftWord rightWord

theorem trace_tariff (ok : replay requests) {k r : Nat} {b : Int}
    (hk : 5≤k) (C : CapTrace k r b) :
    (r<k → 10*b-7*r ≤ 3*(k:ℤ)-13) ∧ (r=k → b≤(k:ℤ)-1) := by
  have price := cap_excludes ok (by omega : 4≤k-1) C.pos C.leftTrace C.rightTrace C.seam
  have h := C.kept
  have hbill := C.bill
  unfold maxBill at price
  split_ifs at price <;> push_cast at price <;> constructor <;> intro hr <;> omega

/-- Conditional only on a correct physical encoding of both caps and
their score ledger (and evaluation of the finite checker). Rank is
computed from the physical subgraphs of the *same* tree. -/
theorem grid_pitch_price (ok : replay requests) {n k : Nat}
    {T A B : SimpleGraph (GridVertex n n)} (tree : IsSpanningSubtree (gridGraph n n) T)
    (hk : 5≤k) (hn : n=3*k+1) (u v : Fin n) (next : u.val+1=v.val)
    (col : Fin (k+1) ↪ Fin n)
    (full : ∀ i, preservesIncidentEdges (gridGraph n n) T (v,col i))
    (ha : A≤T) (hb : B≤T)
    (above : ∀ ⦃x y⦄, A.Adj x y → y.1.val≤u.val)
    (below : ∀ ⦃x y⦄, B.Adj x y → v.val≤x.1.val)
    {a b score : Int}
    (L : CapTrace k (rank A fun i => (u,col i)) a)
    (R : CapTrace k (rank B fun i => (v,col i)) b)
    (ledger : score=n*((k:ℤ)+1)+a+b) :
    score ≤ 3*(k:ℤ)^2+5*k+(3*(k:ℤ)-13)/10 := by
  have sh := grid_shared_rank tree u v next col full ha hb above below
  have l := trace_tariff ok hk L
  have r := trace_tariff ok hk R
  have sum := PitchSkeletonPrice.uniformPitchBonus k _ _ a b (by omega)
    (Int.natCast_nonneg _) (Int.natCast_nonneg _) (by exact_mod_cast sh)
    (by intro e; exact l.1 (by exact_mod_cast e)) (by intro e; exact l.2 (by exact_mod_cast e))
    (by intro e; exact r.1 (by exact_mod_cast e)) (by intro e; exact r.2 (by exact_mod_cast e))
  subst n; push_cast at ledger; linarith only [ledger,sum]

end GridGraphs.PitchCut
