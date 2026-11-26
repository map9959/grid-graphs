import GridGraphs.NoPitch.TailRows.Flow
import GridGraphs.NoPitch.TailRows.StarTransport

namespace GridGraphs.NoPitch.TailRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual Finset
attribute [local irreducible] chart58 chart61
def letters58 (i : Nat) := 3014 ≤ i && i ≤ 3540 && !flow58 i
def letters61 (i : Nat) := 3021 ≤ i && i ≤ 3482 && !flow61 i
def ltable (D : Chart) (sel : Nat → Bool) : Std.HashMap Nat Terms := Id.run do
  let mut tab : Std.HashMap Nat Terms := ∅
  for c in D.cols do
    if c.key%8==3 then
      let n := c.key/8
      let p := n/8100
      let idx := (p/1024*32+p%32)*9+n%90/2%9
      for (i,v) in c.terms do
        if sel i && v>0 then
          let ts := tab[idx]?.getD []
          if !(ts.contains (i,1)) then tab := tab.insert idx ((i,1)::ts)
  return tab
def mark (A : Std.HashMap Nat Terms) (r j : Nat) (a : Letter) := A[(r*32+j)*9+letterNo a]?.getD []

@[noinline] def arcCheck (b : Nat) (w : Nat → Terms) (A : Nat → Nat → Letter → Terms) :=
  decide (∀ r j : J b, ∀ s∈layers (min j.val 4), ∀ a : Letter, permit b j.val s a →
    balanced (w (arcKey (band b r) (prior b j) (band b j) s (advance s a)) ++
      negTerms (A (band b r) (band b j) a)))

def stamp {k} (A : Nat → Nat → Letter → Terms) (x : Site k) (g : Fin 8) (f bits) :=
  let y := turn g x
  if y.1.val%3=0 ∧ y.2.val%3=0 then
    A (axis (N k) 8 y.1.val) (axis (N k) 8 y.2.val) (rotatedLetter g f bits) else []

@[noinline] def checkAt {b} (w : Nat → Terms) (A : Nat → Nat → Letter → Terms) (x : Site b) :=
  decide (∀ (bits : Fin 4 → Bool) (f : Bool) (o : Option (Fin 4)), admissible x bits f o →
    balanced (w (sKey x f bits o) ++ (List.finRange 8).flatMap (fun g => stamp A x g f bits)))

def certLetters (D : Chart) (b : Nat) (sel : Nat → Bool) :=
  let w := contribution D (index D) (prices D sel)
  let A := mark (ltable D sel)
  D.cols.all (fun c => c.key%8<2 || c.key%8==3 || c.terms.all (fun t => !sel t.1)) &&
  decide (∀ i : Fin D.rows.size, sel i → D.rows[i].sense=0 ∧ D.rows[i].rhs=⟨0,0,0⟩) &&
  arcCheck b w A && decide (∀ x : Site b, checkAt w A x)

theorem lettersOK58 : certLetters chart58 19 letters58 := by native_decide
theorem lettersOK61 : certLetters chart61 20 letters61 := by native_decide
theorem letter_counts : ((List.range chart58.rows.size).filter letters58).length=208 ∧
    ((List.range chart61.rows.size).filter letters61).length=203 := by native_decide
end GridGraphs.NoPitch.TailRows
