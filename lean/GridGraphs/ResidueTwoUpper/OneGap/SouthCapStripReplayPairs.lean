import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayFlags

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
namespace GridScan

/-- In sweep coordinates the word gives the previous and next
tile on the near lane, followed by the same pair on the next lane. -/
def seam (axis : Axis) (w : Word) : Word :=
  match axis with
  | .horizontal => w
  | .vertical => (w.1,w.2.2.1,w.2.1,w.2.2.2)

def link (a b : Word) : Bool :=
  (a.2.2.1==b.1) && (a.2.2.2==b.2.1)

/-- Enumerate only chains with agreeing overlapping tile pairs.
This is the input to a two-line strip transition, not an enumeration
of full tile rectangles. -/
def chains (D : Nat → List Word) : Nat → Nat → List (List Word)
  | 0,_ => [[]]
  | k+1,i =>
    let tail := chains D k (i+1)
    (D i).flatMap fun a => (tail.filter fun rest =>
      rest.head?.all (link a)).map (a::·)

def chainOf (w : Nat → Word) : Nat → Nat → List Word
  | 0,_ => []
  | k+1,i => w i :: chainOf w k (i+1)

theorem chainOf_mem (D : Nat → List Word) (w : Nat → Word) (k i : Nat)
    (mem : ∀ j<k, w (i+j)∈D (i+j))
    (compat : ∀ j, j+1 < k → link (w (i+j)) (w (i+j+1))=true) :
    chainOf w k i∈chains D k i := by
  induction k generalizing i with
  | zero => simp [chainOf,chains]
  | succ k ih =>
    simp only [chainOf,chains,List.mem_flatMap,List.mem_map,List.mem_filter]
    refine ⟨w i,by simpa using mem 0 (by omega),chainOf w k (i+1),⟨?_,?_⟩,rfl⟩
    · apply ih
      · intro j jl
        simpa only [Nat.add_assoc,Nat.add_comm 1 j] using mem (1+j) (by omega)
      · intro j jl
        simpa only [Nat.add_assoc] using compat (1+j) (by omega)
    · cases k with
      | zero => rfl
      | succ k =>
        simpa [chainOf] using compat 0 (by omega)

/-- A pair of physical consecutive lines contributes a legal
compatible chain whenever all its plaquettes are in the domains.
This is the coverage direction needed to trust strip deletions. -/
theorem sweep_chain_covered {H W : Nat} (s : Window H W) (D : Nat → Nat → List Word)
    (b : Tiles) (j : Nat) (hj : j+2 ≤ s.length)
    (consistent : s.Consistent (fun r c m => m∈D r c) b) :
    let w := fun i => seam s.axis (acrossWord s.axis b j i)
    let bank := fun i =>
      (D (cell s.axis s.start j i).1 (cell s.axis s.start j i).2).map (seam s.axis)
    chainOf w (s.depth-1) 0∈chains bank (s.depth-1) 0 := by
  dsimp only
  apply chainOf_mem
  · intro i hi
    simp only [Nat.zero_add]
    exact List.mem_map.mpr ⟨_,consistent j i hj (by omega),rfl⟩
  · intro i _
    cases ax : s.axis <;> simp [seam,acrossWord,link]

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
