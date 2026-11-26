import GridGraphs.NoPitch.TailRows.LineTransport
import GridGraphs.NoPitch.Budget.Flow19

namespace GridGraphs.NoPitch.TailRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual TailCoverage Finset
attribute [local irreducible] chart58 chart61

def flow58 (i : Nat) := (3042 ≤ i && i ≤ 3090) || (3121 ≤ i && i ≤ 3157) ||
  (3185 ≤ i && i ≤ 3222) || (3253 ≤ i && i ≤ 3306) || (3335 ≤ i && i ≤ 3373) ||
  (3405 ≤ i && i ≤ 3449) || (3484 ≤ i && i ≤ 3540)
def flow61 (i : Nat) := (3053 ≤ i && i ≤ 3103) || (3127 ≤ i && i ≤ 3158) ||
  (3193 ≤ i && i ≤ 3229) || (3264 ≤ i && i ≤ 3312) || (3345 ≤ i && i ≤ 3378) ||
  (3408 ≤ i && i ≤ 3444) || (3464 ≤ i && i ≤ 3482)

/-- Sparse list of row ids attached to each (row band, slot band, state).
The positive entries merely suggest a potential; `localCheck` verifies
both signs for each arc, including any nonexistent chart key. -/
def table (D : Chart) (sel : Nat → Bool) : Std.HashMap Nat Terms := Id.run do
  let mut a : Std.HashMap Nat Terms := ∅
  for c in D.cols do
    if c.key%8==3 then
      let n := c.key/8
      let p := n/8100
      let key := (p/1024*32+p%32)*90+n%90
      for (i,v) in c.terms do
        if sel i && v>0 then
          let ts := a[key]?.getD []
          if !(ts.contains (i,1)) then a := a.insert key ((i,1)::ts)
  return a
def node (a : Std.HashMap Nat Terms) (r j : Nat) (s : State) := a[(r*32+j)*90+state s]?.getD []

@[noinline] def localCheck (b : Nat) (w : Nat → Terms) (A : Nat → Nat → State → Terms) :=
  decide (∀ r j : J b, ∀ s∈layers (min j.val 4), ∀ l : Letter, permit b j.val s l →
    let t := advance s l
    let a := if j.val=0 then [] else A (band b r) (band b (j.val-1)) s
    let c := if j.val=b then [] else A (band b r) (band b j) t
    balanced (w (arcKey (band b r) (prior b j) (band b j) s t) ++ a ++ negTerms c))
def certified (D : Chart) (b : Nat) (sel : Nat → Bool) :=
  D.cols.all (fun c => c.key%8==3 || c.terms.all (fun t => !sel t.1)) &&
  decide (∀ i : Fin D.rows.size, sel i → D.rows[i].sense=0 ∧ D.rows[i].rhs=⟨0,0,0⟩) &&
  localCheck b (contribution D (index D) (prices D sel)) (node (table D sel))

private theorem ok58 : certified chart58 19 flow58 := by native_decide
private theorem ok61 : certified chart61 20 flow61 := by native_decide
theorem counts : ((List.range chart58.rows.size).filter flow58).length=319 ∧
    ((List.range chart61.rows.size).filter flow61).length=259 := by native_decide

theorem lifted_row {D : Chart} {k b : Nat} {sel : Nat → Bool} (baseOK : certified D b sel)
    (hb : 19≤b) (hk : b≤k) (F : Finset (Site k))
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (o : Site k → Option (Fin 4)) (i : Fin D.rows.size) (h : sel i) (t : Int) :
    rowHolds D.rows[i].sense (2*lhs D (physicalVector D F o) i) (8*D.rows[i].rhs.atStep t) := by
  obtain ⟨first,test⟩ := Bool.and_eq_true_iff.mp baseOK
  obtain ⟨sup,metaInfo⟩ := Bool.and_eq_true_iff.mp first
  let A := node (table D sel)
  have law : LocalLaw b (lookupPrice D i (index D)) (fun y j s => coeff i (A y j s)) := by
    intro r j s hs l pass
    have eq := zero_of_balanced _ (of_decide_eq_true test r j s hs l pass) i
    rw [coeff_append,coeff_append,coeff_neg,sig_price D sel i h] at eq
    have zero : coeff i []=0 := rfl
    by_cases start : j.val=0 <;> by_cases last : j.val=b <;>
      simp only [before,after,start,last,if_true,if_false,zero,A,
        if_neg (by omega : b≠0),if_neg (by omega : 0≠b)] at eq ⊢ <;> omega
  have z := physical_line_zero hb hk law F (all_views_np F rows cols)
  have m := of_decide_eq_true metaInfo i h
  rw [line_only_lhs F o i sel h sup,z,m.1,m.2]; simp [rowHolds,Poly.atStep]

def selected (k : Nat) := if k%2=1 then flow58 else flow61
theorem flow_tail {k : Nat} (hk : 19≤k) (F : Finset (Site k))
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (o : Site k → Option (Fin 4)) :
    ∀ i : Fin (tailChart k).rows.size, selected k i → ∀ t : Int,
    rowHolds (tailChart k).rows[i].sense (2*lhs (tailChart k) (physicalVector (tailChart k) F o) i)
      (8*(tailChart k).rows[i].rhs.atStep t) := by
  let b := if k%2=1 then 19 else 20
  have ok : certified (tailChart k) b (selected k) := by
    by_cases odd : k%2=1 <;> simp [b,tailChart,selected,odd,ok58,ok61]
  exact lifted_row ok (by dsimp [b]; split <;> decide) (by dsimp [b]; split <;> omega) F rows cols o

/-- Drop the flow rows from the equality premise of the uniform physical
upper. Transport applies to arbitrary orientations; here specialize to
the single junction-rooted orientation used by the rest of the ledger. -/
theorem upper_of_remaining {k : Nat} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (rest : ∀ i : Fin (tailChart k).rows.size, (tailChart k).rows[i].sense=0 → ¬selected k i →
      2*lhs (tailChart k) (physicalVector (tailChart k) F (out F)) i =
        8*(tailChart k).rows[i].rhs.atStep ((k-19)/2 : Nat)) : F.card ≤ squareScore (N k) := by
  apply tail_upper_of_equalities hk F acy
  intro i eq
  by_cases s : selected k i
  · have e := flow_tail hk F rows cols (out F) i s (((k-19)/2 : Nat):Int)
    rw [eq] at e; exact e
  · exact rest i eq s

end GridGraphs.NoPitch.TailRows
