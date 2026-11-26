import GridGraphs.NoPitch.TailRows.PatchTransport
import GridGraphs.NoPitch.TailRows.Buckets58
import GridGraphs.NoPitch.TailRows.Buckets61

namespace GridGraphs.NoPitch.TailRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual Finset
attribute [local irreducible] chart58 chart61
def normal (B : Array NormShape) (i : Nat) := 1 ≤ i && i ≤ B.size
def starFine {k} (x : Site k) (g : Fin 8) := fine (N k) 8 (turn g x).1.val (turn g x).2.val
def orbitMass (f : Fin 8 → List Nat) (pat : List Nat) : Int :=
  ∑ g, if f g=pat then 1 else 0

/-- Each of the eight *oriented* positions contributes a unit when it
matches this row's target. No division by an assumed orbit size. -/
def expected (B : Array NormShape) (h : Nat) (f : Fin 8 → List Nat) : Terms := Id.run do
  let views := Vector.ofFn f
  let mut ts := []
  for j in [:B.size] do
    let v := B[j]!
    if v.collar=h then
      let w : Int := ∑ g : Fin 8, if views[g]=v.pattern then 1 else 0
      if w != 0 then ts := (j+1,w)::ts
  return ts

-- The individual coefficients of `expected` will also be checked
-- against all target rows at once, outside the state enumeration.
@[noinline] def expectOK (B : Array NormShape) (h : Nat) (views : Fin 8 → List Nat) (ts : Terms) :=
  decide (∀ j : Fin B.size, coeff (j.val+1) ts =
    if B[j.val]!.collar=h then orbitMass views B[j.val]!.pattern else 0)
@[noinline] def starNormAt {b} (w : Nat → Terms) (x : Site b) (ts : Terms) :=
  decide (∀ (bits : Fin 4 → Bool) (f : Bool) (o : Option (Fin 4)), admissible x bits f o →
    balanced (w (sKey x f bits o) ++ negTerms ts))
@[noinline] def patchNormAt {b} (w : Nat → Terms) (p : PatchPos b) (ts : Terms) :=
  decide (∀ a : Nine, legal a → balanced (w (patchCode p a) ++ negTerms ts))

def normCert (D : Chart) (b : Nat) (B : Array NormShape) :=
  let w := contribution D (index D) (prices D (normal B))
  supported D (normal B) &&
  decide (∀ j : Fin B.size, let i := j.val+1
    ∃ hi : i<D.rows.size, (D.rows[i]'hi).sense=0 ∧ (D.rows[i]'hi).rhs=B[j.val]!.polynomial ∧
      ((B[j.val]!.collar=8 ∧ B[j.val]!.n=N b) ∨ (B[j.val]!.collar=7 ∧ B[j.val]!.n=N b-2))) &&
  decide (∀ x : Site b, let vs := starFine x; let s := expected B 8 vs
    expectOK B 8 vs s && starNormAt w x s) &&
  decide (∀ p : PatchPos b, let vs := patchFine p; let s := expected B 7 vs
    expectOK B 7 vs s && patchNormAt w p s)

theorem norm58 : normCert chart58 19 buckets58 := by native_decide
theorem norm61 : normCert chart61 20 buckets61 := by native_decide

end GridGraphs.NoPitch.TailRows
