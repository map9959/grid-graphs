import GridGraphs.ResidueTwoUpper.TwoGapOwnerBits

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
open ResidueZero Stencil Words BoundarySix.Connected

/-- Offsets are row, column, with origin the NW corner of the 6×6
projection. The physical test has a four-site halo. `field` is allowed
on the one-site fringe beyond the halo for partial ownership clauses. -/
structure Field where
  mark : Pos → Bool
  dir : Pos → Nat
  sheet : Pos → Bool
  ext : Pos → Nat → Bool
  fs : Pos → Nat → Bool

def shiftAt (i j : Int) (p : Pos) : Pos := (site j p.1,site i p.2)
def plus3 (p : Pos) (b : Fin 9) : Pos := p+offset b.val
def packed9 (f : Fin 9 → Bool) := ((List.finRange 9).map fun z => (f z).toNat <<< z.val).sum
theorem packed_iff : ∀ f : Fin 9 → Bool, packed9 f<512 ∧ ∀ i : Fin 9, bit (packed9 f) i=(f i).toNat := by native_decide
def patchAt (l : Field) (p : Pos) := packed9 fun b => l.mark (plus3 p b)
def nbrAt (l : Field) (p : Pos) := code fun d => l.mark (shift p d)

/-- Producer order: four tiles NW, SW, NE, SE; within each tile the row
index changes fastest. This is the order of the 36 projection literals in
`two_gap_mask_tables.local`, not the row-major `maskAt` order. -/
def four (l : Field) (t : Fin 4) := packed9 fun b =>
  l.mark (3*(t.val%2)+(b.val%3:Nat),3*(t.val/2)+(b.val/3:Nat))
def halo (p : Pos) := -4≤p.1 ∧ p.1≤9 ∧ -4≤p.2 ∧ p.2≤9

def sig (k q i j : Int) (p : Pos) :=
  let v := shiftAt i j p
  let n := 3*k+2
  (inside n v, inside (n-1) v, rimDatum k q v.2 v.1,
    decide (v.1=0 ∧ v.2=0), decide (v.1=0 ∧ v.2=2+3*q),
    representative 23 (k-7) v, representative 21 (k-7) v)

abbrev Stamp := Bool × Bool × (Option Bool × Nat × Bool) × Bool × Bool × Pos × Pos
def onB (s : Pos → Stamp) (p : Pos) := (s p).1
def cellB (s : Pos → Stamp) (p : Pos) := (s p).2.1
def rimAt (s : Pos → Stamp) (p : Pos) := (s p).2.2.1
def rootAt (s : Pos → Stamp) (p : Pos) := (s p).2.2.2.1
def exitAt (s : Pos → Stamp) (p : Pos) := (s p).2.2.2.2.1
def starPos (s : Pos → Stamp) (p : Pos) := (s p).2.2.2.2.2.1
def patchPos (s : Pos → Stamp) (p : Pos) := (s p).2.2.2.2.2.2
def core (s : Pos → Stamp) (p : Pos) := halo p ∧ onB s p=true
def arc (l : Field) (p : Pos) (d : Fin 4) := l.dir p=d.val

structure Local (s : Pos → Stamp) (l : Field) : Prop where
  off : ∀ p, halo p → ¬onB s p → l.mark p=false
  rim : ∀ p, core s p → ∀ b, (rimAt s p).1=some b → l.mark p=b
  parents : ∀ p, core s p → (rimAt s p).2.1<5 → l.dir p=(rimAt s p).2.1
  corner : ∀ p, core s p → (starPos s p).1∈[0,22] → (starPos s p).2∈[0,22] → l.mark p
  tooth : ∀ p, core s p → (rimAt s p).2.2 → l.mark p → l.dir p=3
  star : ∀ p, core s p →
    let f := (l.mark p).toNat; let nb := nbrAt l p; let o := l.dir p
    o<5 ∧ starOK 23 (starPos s p) f nb o ∧
    (if rootAt s p then o=4 else o=4 → f=0 ∧ nb=0) ∧
    twoOrbitStar 23 (starPos s p) f nb o=(if exitAt s p then full else 0)
  patch : ∀ p, halo p → (∀ b : Fin 9, onB s (plus3 p b)) →
    maskOK (patchAt l p) ∧ twoOrbitPatch 23 (patchPos s p) (patchAt l p)=0
  bonds : ∀ p, core s p → ∀ d : Fin 4, onB s (shift p d) →
    let z := shift p d; let rev : Fin 4 := ⟨(d.val+2)%4,by omega⟩
    ((arc l p d ∨ arc l z rev) ↔ (l.mark p || l.mark z)=true) ∧ ¬(arc l p d ∧ arc l z rev)
  turns : ∀ p, core s p → ∀ d e : Fin 4, arc l p d → arc l (shift p d) e →
    l.sheet (shift p d)=xor (l.sheet p) (wrap d e)
  extSites : ∀ p, core s p →
    zeroOrOne (!l.mark p && (List.range 4).all (fun d => !l.mark (shift p d))) (fun d => l.ext p d)
  faces : ∀ p, halo p → cellB s p → zeroOrOne true (fun d => l.fs p d)
  faceOff : ∀ p, halo p → ¬cellB s p → ∀ d, l.fs p d=false
  extOff : ∀ p, core s p → ∀ d : Fin 4, ¬onB s (shift p d) → l.ext p d=false
  freeEdges : ∀ p, core s p → ∀ v, onB s (edgeBase p v) →
    zeroOrOne (!(l.mark p || l.mark (edgeBase p v))) (picks l.ext l.fs p v)

def admitted (k q i j : Int) (tiles : Fin 4 → Nat) := ∃ l, Local (sig k q i j) l ∧ four l=tiles

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
