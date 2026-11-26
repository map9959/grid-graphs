import GridGraphs.ResidueZero.Budget
import GridGraphs.ResidueZero.PhysicalStar

/-! Global accounting of the non-cancelling terms. Coordinates are
reindexed separately at the site and patch-origin side lengths. -/
namespace GridGraphs.ResidueZero
open Finset

private def rev {s : Nat} (i : Fin s) : Fin s := ⟨s-1-i.val,by omega⟩
private theorem rev_rev {s : Nat} (i : Fin s) : rev (rev i) = i := by
  apply Fin.ext; dsimp [rev]; omega
private theorem rev_coord {s : Nat} (i : Fin s) : ((rev i).val:Int) = (s:Int)-1-i.val := by
  dsimp [rev]; omega

private def reflect (s : Nat) : GridVertex s s ≃ GridVertex s s where
  toFun p := (p.1,rev p.2)
  invFun p := (p.1,rev p.2)
  left_inv p := by simp [rev_rev]
  right_inv p := by simp [rev_rev]

private def spin (s : Nat) : GridVertex s s ≃ GridVertex s s where
  toFun p := (p.2,rev p.1)
  invFun p := (rev p.2,p.1)
  left_inv p := by simp [rev_rev]
  right_inv p := by simp [rev_rev]

def symmetry (s g : Nat) : GridVertex s s ≃ GridVertex s s :=
  let f := if 4≤g then reflect s else Equiv.refl _
  f.trans (match g%4 with
    | 0 => Equiv.refl _
    | 1 => spin s
    | 2 => (spin s).trans (spin s)
    | _ => (spin s).symm)

theorem coord_symmetry {s : Nat} (g : Nat) (p : GridVertex s s) :
    coord (symmetry s g p) = image s g (coord p) := by
  unfold symmetry image
  have hg : g%4=0 ∨ g%4=1 ∨ g%4=2 ∨ g%4=3 := by omega
  rcases hg with hg|hg|hg|hg <;> by_cases h : 4≤g <;> simp [hg,h,reflect,spin,coord,rev_coord]

theorem sum_image {s : Nat} (g : Nat) (f : Pos → Int) :
    (∑ p : GridVertex s s, f (image s g (coord p))) = ∑ p : GridVertex s s, f (coord p) := by
  simp_rw [← coord_symmetry]
  exact (symmetry s g).sum_comp (f ∘ coord)

theorem sum_norm (s d : Nat) (tab : Std.HashMap Nat Int) :
    (∑ p : GridVertex s s, tab.getD (atPos s d (coord p)) 0) = plane s d (charge tab) := by
  rw [Fintype.sum_prod_type]
  unfold plane axisSum charge atPos coord
  let f (i j : Nat) := tab.getD ((axis s d i).toNat*16+(axis s d j).toNat) 0
  change (∑ i : Fin s, ∑ j : Fin s, f i j) = ∑ i ∈ range s, ∑ j ∈ range s, f i j
  simp_rw [Fin.sum_univ_eq_sum_range (f _) s]
  exact Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range s, f i j) s

theorem sum_norm_image (s d g : Nat) (tab : Std.HashMap Nat Int) :
    (∑ p : GridVertex s s, tab.getD (atPos s d (image s g (coord p))) 0) =
    plane s d (charge tab) :=
  (sum_image g (fun p => tab.getD (atPos s d p) 0)).trans (sum_norm s d tab)

theorem sum_mark {n : Nat} (F : Finset (GridVertex n n)) :
    (∑ p : GridVertex n n, ((decide (p∈F)).toNat:Int)) = F.card := by
  have h (p : GridVertex n n) : ((decide (p∈F)).toNat:Int) = if p∈F then 1 else 0 := by
    by_cases hp : p∈F <;> simp [hp]
  simp [h]

private theorem cornerPrice (i : Nat) :
    cornerPrices.getD i 0 = if i=0 then -(scale/2) else 0 := by
  have sing : cornerPrices = (∅ : Std.HashMap Nat Int).insert 0 (-(scale/2)) := by rfl
  by_cases h : i=0
  · subst i; native_decide
  · simp [sing,Std.HashMap.getD_insert,h,Ne.symm h]

theorem corner_nonpos (n : Nat) (p : Pos) (o : Nat) :
    (if o=4 then 4*cornerPrices.getD (atPos n 6 p) 0 else 0) ≤ 0 := by
  rw [cornerPrice]; split_ifs <;> decide

/-- The distinguished corner is the origin in exactly two of the views
for every side ≥ 12. Its root bill alone pays the required average. -/
theorem root_corner_sum {n : Nat} (hn : 12≤n) :
    ((List.range 8).map fun g => 4*cornerPrices.getD (atPos n 6 (image n g (0,0))) 0).sum =
      8*cornerPrices.getD 0 0 := by
  have lo : axis n 6 0=0 := by unfold axis; split_ifs <;> omega
  have hi : axis n 6 ((n:Int)-1)=14 := by unfold axis; split_ifs <;> omega
  simp [show List.range 8=[0,1,2,3,4,5,6,7] by decide,cornerPrice,image,atPos,lo,hi,scale]

end GridGraphs.ResidueZero
