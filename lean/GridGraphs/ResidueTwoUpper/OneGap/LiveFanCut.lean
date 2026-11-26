import GridGraphs.ResidueTwoUpper.OneGap.EastBoundaryRows
import GridGraphs.ResidueTwoUpper.OneGap.GuardedSchedules
import GridGraphs.ResidueTwoUpper.OneGap.FanNorthScan

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.LiveCut
open ResidueZero Stencil L7 FanSlab Short FanSeed EastBoundary BoundarySix.Connected SouthCap

def mword (b i : Nat) := if i+3<b then 56 else if i+3=b then 24 else
  if i+2=b then 12 else if i+1=b then 6 else 7
theorem eastern {q j i : Nat} (pos : 1≤j) (middle : 6*j+2≤q) (lo : 3*j+1 ≤ i) :
    history q j i=mword (q+2-3*j) i := by
  unfold history actual word mword
  split_ifs <;> first | rfl | omega |
    (rw [show i-(3*j-2+3+(q-6*j-2))=0 by omega]; decide) |
    (rw [show i-(3*j-2+3+(q-6*j-2))=1 by omega]; decide) |
    (rw [show i-(3*j-2+3+(q-6*j-2))=2 by omega]; decide)
theorem read_edge {u F w q j i} (R : Read (35+42*u) q j F w)
    (jp : 1≤j) (mid : 6*j+2≤q) (lo : 3*j+1 ≤ i) (hi : i<11+14*u) :
    maskAtTile F w j i=edge (q+2-3*j) i := by
  let m := mword (q+2-3*j) i
  have bd : m<512 := by unfold m mword; split_ifs <;> decide
  have eq : transpose m=edge (q+2-3*j) i := by unfold m mword edge; split_ifs <;> rfl
  rw [←eq]; apply align _ _ _ _ _ bd
  intro a b
  simpa only [eastern jp mid lo] using R i a b (by have := a.isLt; omega) a.isLt b.isLt

def fits (k q : Nat) :=
  let y := (q-15)/6+2
  Guarded.atCut k q y (q+2-3*y+1)

/-- Read the *current* tooth rather than keeping the column of the
tooth two rows earlier. Newly used dangling tips are sealed in their
own two-column collars. The old front supplies the actual north feet. -/
theorem exclude {u F w q P} (S : Seed (u:=u) F P w q)
    (H : PhysicalHalo u F w q (fanDirection u w)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) (score : F.card=440+1020*u+588*u^2)
    (big : 57≤q) (ok : fits (11+14*u) q)
    (old : Front F w q (11+14*u) ((q-15)/6+2) (q-3*((q-15)/6)+3)) : False := by
  let z := (q-15)/6; let y := z+2; let b := q+2-3*y
  have room := S.room
  have loc : q+2=b+3*y := by dsimp [b,y,z]; omega
  have mid : 6*y+2≤q := by dsimp [y,z]; omega
  have yl : 8≤y := by dsimp [y,z]; omega
  have R := north_rows north_output u q big room S.odd F acy w P S.step S.clean
    (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero) S.west
    (by rw [tile_eq F w (by omega)]; exact S.paid)
    (fun i lo hi => by rw [tile_eq F w (by omega)]; exact S.east i lo hi)
  have tooth := at_tile S acy (seed:=0) (i:=b) (b:=b) (z:=z) .boundary (by simp)
    (by dsimp [z]; omega) loc le_rfl (by omega) (by omega) (by omega) (by dsimp [y] at *; omega)
    (by
      intro _ a ha k hk
      have edge' := read_edge (R (z+a) (by dsimp [z]; omega))
        (i:=b-4+k) (by dsimp [y] at *; omega) (by dsimp [y] at *; omega)
        (by dsimp [y] at *; omega) (by omega)
      rwa [show q+2-3*(z+a)=b+(6-3*a) by dsimp [y] at *; omega] at edge')
    (by intro h; omega)
  have plain (i : Nat) (lo : b ≤ i) (hi : i<11+14*u) : maskAtTile F w y i=73 := by
    induction i,lo using Nat.le_induction with
    | base => simpa [edge] using tooth
    | succ i _ ih =>
      apply east_step u q y i (by omega) (by omega) (by omega) F acy w P S.step S.clean
        (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero) (ih (by omega))
  apply Guarded.exclude_from H acy one score (by omega) room (y:=y) (f:=b+1) ok
    (by omega) (by omega) (by push_cast; omega)
  · refine ⟨fun r lo hi i il ih => (show r=y by omega) ▸ plain i (by omega) ih,?_,?_⟩
    · intro t tl th right
      apply dangling_in_collar _ q y t mid (by omega) (by omega) (by omega) right
      intro j jh i a e it ti bound al el
      by_cases prev : j≤z+1
      · exact R j prev i a e bound al el
      obtain rfl : j=y := by dsimp [y] at *; omega
      rw [eastern (by omega) mid (by omega),show mword (q+2-3*y) i=7 by
        unfold mword; split_ifs <;> omega]
      have v := plateau_bit (plain i (by omega) (by omega)) ⟨a,al⟩ ⟨e,el⟩
      have tab : ∀ a e : Fin 3, (decide (a.val=0)).toNat=lane 7 (3*a.val+e.val) := by decide
      exact v.trans (tab ⟨a,al⟩ ⟨e,el⟩)
    · intro t _ hi rt; exact old.2.2 t (by dsimp [z] at *; omega) hi rt
  · intro r rl rh i il ih
    obtain rfl : r=y := by omega
    exact plain i (by omega) ih
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.LiveCut
