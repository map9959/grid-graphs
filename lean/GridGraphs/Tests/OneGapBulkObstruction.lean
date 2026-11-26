import GridGraphs.ResidueTwoUpper.StencilLocal

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open ResidueZero Stencil

private def stripe (r _ : Nat) := r%3==0
private def arrow (r _ : Nat) : Nat := if r%3=0 then 0 else if r%3=1 then 3 else 1

private def tile (r c : Nat) := ((List.range 9).map fun i =>
  (stripe (r+i/3) (c+i%3)).toNat <<< i).sum
private def nb (m : Nat) := bit m 5 + 2*bit m 7 + 4*bit m 3 + 8*bit m 1
private def owns (a b m n : Bool) := ((a != b) == (m || n)) && !(a && b)
private def rank (r c : Nat) := c + (stripe r c).toNat

/-- In an open bulk rectangle, horizontal stripes obey the local mark
prices and forced-bond ownership. Their aligned mask passes both axis
filters but is not a straight-mask tag for the fan speed replay. The
scored forest's actual boundaries or another global invariant are needed. -/
theorem open_bulk_obstruction :
    (∀ r c : Fin 3,
      let m := tile r c
      let p : Pos := ((8:ℤ)+r.val,(8:ℤ)+c.val)
      let o := arrow (r.val+1) c.val
      maskOK m ∧ twoOrbitPatch 35 (p-(1,1)) m=0 ∧
      starOK 35 p (bit m 4) (nb m) o ∧ twoOrbitStar 35 p (bit m 4) (nb m) o=0) ∧
    (∀ r c, owns (arrow r c==0) (arrow r (c+1)==2) (stripe r c) (stripe r (c+1)) ∧
      owns (arrow r c==1) (arrow (r+1) c==3) (stripe r c) (stripe (r+1) c)) ∧
    (∀ r c, (arrow r c=0 → rank r c<rank r (c+1)) ∧
      (arrow r c=1 → rank r c<rank (r+1) c) ∧
      (arrow r c=3 → rank r c<rank (r-1) c)) ∧
    (∀ r c, tile (3*r) (3*c)=7) ∧ (7 &&& 16 : Nat)=0 := by
  refine ⟨by native_decide,?_,?_,?_,by decide⟩
  · intro r c
    have hr : r%3=0 ∨ r%3=1 ∨ r%3=2 := by omega
    rcases hr with h|h|h <;>
      simp [owns,stripe,arrow,h,show (r+1)%3=(r%3+1)%3 by omega]
  · intro r c
    have hr : r%3=0 ∨ r%3=1 ∨ r%3=2 := by omega
    rcases hr with h|h|h
    · simp [rank,stripe,arrow,h]
    · have prev : (r-1)%3=0 := by omega
      simp [rank,stripe,arrow,h,prev]
    · have next : (r+1)%3=0 := by omega
      simp [rank,stripe,arrow,h,next]
  · intro r c
    have phase (i : Nat) : (3*r+i/3)%3=(i/3)%3 := by omega
    simpa only [tile,stripe,phase,Nat.zero_add] using (show tile 0 0=7 by decide)

#print axioms open_bulk_obstruction

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
