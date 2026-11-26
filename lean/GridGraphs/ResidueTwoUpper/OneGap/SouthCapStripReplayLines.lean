import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripForward

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
namespace GridScan

abbrev Line := List Nat

def linesOf : List Word → Line × Line
  | [] => ([],[])
  | [w] => ([w.1,w.2.2.1],[w.2.1,w.2.2.2])
  | w::a::as =>
    let next := linesOf (a::as)
    (w.1::next.1,w.2.1::next.2)

def lineOf (f : Nat → Nat) : Nat → Nat → Line
  | 0,_ => []
  | n+1,i => f i :: lineOf f n (i+1)

theorem lineOf_getD (f : Nat → Nat) (n start i : Nat) (hi : i<n) :
    ((lineOf f n start)[i]?.getD 0)=f (start+i) := by
  induction n generalizing start i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [lineOf]
    | succ i =>
      simpa [lineOf,Nat.add_assoc,Nat.add_comm 1 i] using ih (start+1) i (by omega)

private theorem linesOf_chainOf (f g : Nat → Nat) (k start : Nat) :
    linesOf (chainOf (fun i => (f i,g i,f (i+1),g (i+1))) (k+1) start) =
      (lineOf f (k+2) start,lineOf g (k+2) start) := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
    simp only [chainOf,linesOf,lineOf]
    have next := ih (start+1)
    simp only [chainOf] at next
    rw [next]
    rfl

def pairTable {H W : Nat} (s : Window H W) (D : Nat → Nat → List Word) (j : Nat) :
    List (Line × Line) :=
  (chains (fun i => (D (cell s.axis s.start j i).1 (cell s.axis s.start j i).2).map (seam s.axis))
    (s.depth-1) 0).map linesOf

theorem pairTable_cover {H W : Nat} (s : Window H W) (D : Nat → Nat → List Word)
    (b : Tiles) (j : Nat) (hj : j+2 ≤ s.length)
    (h : s.Consistent (fun r c m => m∈D r c) b) :
    (lineOf (b j) s.depth 0,lineOf (b (j+1)) s.depth 0)∈pairTable s D j := by
  have candidate := sweep_chain_covered s D b j hj h
  dsimp only at candidate
  have orient : (fun i => seam s.axis (acrossWord s.axis b j i)) =
      fun i => (b j i,b (j+1) i,b j (i+1),b (j+1) (i+1)) := by
    funext i
    cases ax : s.axis <;> simp [seam,acrossWord]
  refine List.mem_map.mpr ⟨_,candidate,?_⟩
  rw [orient,show s.depth-1=(s.depth-2)+1 by have := s.depth_min; omega,linesOf_chainOf]
  rw [show s.depth-2+2=s.depth by have := s.depth_min; omega]

def readLine (l : Line) (i : Nat) : Nat := l[i]?.getD 0

def wordOf (axis : Axis) (a b : Line) (i : Nat) : Word :=
  match axis with
  | .horizontal => (readLine a i,readLine b i,readLine a (i+1),readLine b (i+1))
  | .vertical => (readLine a i,readLine a (i+1),readLine b i,readLine b (i+1))

theorem wordOf_lines {H W : Nat} (s : Window H W) (b : Tiles) (j i : Nat)
    (hi : i+2 ≤ s.depth) :
    wordOf s.axis (lineOf (b j) s.depth 0) (lineOf (b (j+1)) s.depth 0) i =
      acrossWord s.axis b j i := by
  have lo : i<s.depth := by omega
  have hi' : i+1<s.depth := by omega
  cases ax : s.axis <;>
    simp only [wordOf,acrossWord,readLine,lineOf_getD _ _ _ _ lo,lineOf_getD _ _ _ _ hi',Nat.zero_add]

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
