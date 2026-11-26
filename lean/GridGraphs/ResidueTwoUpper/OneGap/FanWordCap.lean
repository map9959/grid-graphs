import GridGraphs.ResidueTwoUpper.OneGap.FanCollision
import GridGraphs.ResidueTwoUpper.OneGap.TrimmedCap

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
open L7 FanSlab ResidueZero BoundarySix.Connected SouthCap SouthCap.Strip.GridScan

/-- Before the central fan segment disappears, the eastern suffix
of its row word starts at `q-3*y+2`, independently of the board size. -/
theorem known_row_suffix {u q y F w} (known : Known u q y F w)
    (pos : 1≤y) (center : 6*y+2≤q) {i : Nat}
    (start : q-3*y+2 ≤ i) (inside : i<11+14*u) :
    square F w (1+3*y) (1+3*i)=73 := by
  have mask : actual q y i=7 := by
    unfold actual word
    split_ifs <;> omega
  change square F w (1+3*y) (1+3*i)=transpose 7
  apply align F w y i 7 (by decide)
  intro a b
  have h := known b b.isLt (3*i+a) (by have := a.isLt; omega)
  rw [show (3*i+a)/3=i by have := a.isLt; omega,mask,
    show (3*i+a)%3=a by have := a.isLt; omega] at h
  simpa only [Nat.add_assoc] using h

/-- Interface for a structural seed/propagation argument. No
row-specific crop is needed once the seed supplies the row word. -/
theorem exclude_of_known_row {u q y F w} (H : PhysicalHalo u F w q (fanDirection u w))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (yl : 4≤y) (ht : y+14≤11+14*u) (center : 6*y+2≤q)
    (known : Known u q y F w) (line : RootLine F w (11+14*u-1) y)
    (space : q-3*y+2+topWidth (11+14*u-y)≤11+14*u) : False := by
  exact trimmed_excludes H acy one score hk yl (by omega) ht space
    (fun i lo hi => known_row_suffix known (by omega) center lo hi) line
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot
