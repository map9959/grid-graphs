import GridGraphs.ResidueTwoUpper.OneGap.FanBootData
import GridGraphs.ResidueTwoUpper.OneGap.FanStep
import GridGraphs.ResidueTwoUpper.OneGap.PatchFilter

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open FanSlab FanBoot ResidueZero Stencil

private abbrev Marks := Nat → Nat → Bool
private abbrev Arrows := Nat → Nat → Fin 4
private def owns (a b m n : Bool) := ((a != b) == (m || n)) && !(a && b)

private def marks : Array Nat := #[
  153391689, 153391689, 153391689, 153391689, 153391689, 153391689,
  153391689, 153391689, 153391689, 153391689, 153391689, 153391689,
  153391689, 153391688, 153391682, 153391634, 153391250, 153388178,
  153363602, 153166994, 151594130, 139011218, 575218834, 0, 536870908,
  1, 0, 1073741822, 0, 536870913]

private def arrows : Array Nat := #[
  0x2cb2cb2cb2cb2cb, 0x2cb2cb2cb2cb2cb, 0x2cb2cb2cb2cb2cb,
  0x2cb2cb2cb2cb2cb, 0x2cb2cb2cb2cb2cb, 0x2cb2cb2cb2cb2cb,
  0x2cb2cb2cb2cb2cb, 0x2cb2cb2cb2cb2cb, 0x2cb2cb2cb2cb2cb,
  0x2cb2cb2cb2cb2cb, 0x2cb2cb2cb2cb2cb, 0x2cb2cb2cb2cb2cb,
  0x2cb2cb2cb2cb2cb, 0x2cb2cb2cb2cb2c7, 0x2cb2cb2cb2cb1e4,
  0x2cb2cb2cb2c7924, 0x2cb2cb2cb1e4924, 0x2cb2cb2c7924924,
  0x2cb2cb1e4924924, 0x2cb2c7924924924, 0x2cb1e4924924924,
  0x6c792492492492a, 0x4e492492492492c, 0x15555555555555e,
  0x1, 0x3fffffffffffff9, 0x555555555555556, 0x0, 0xffffffffffffffe, 0xc5555555555555b]

private def M : Marks := fun r c => marks[r]!.testBit c
private def A : Arrows := fun r c => Fin.ofNat 4 (arrows[r]! >>> (2*c))
def winMask (M : Marks) (r c : Nat) := bits fun i => M (r+i.val/3) (c+i.val%3)

private def priced (r c m o : Nat) : Bool :=
  let x := (7+r%3 : Nat); let y := (7+c%3 : Nat)
  maskOK m && (twoOrbitPatch 35 (x,y) m==0) &&
    starOK 35 (x+1,y+1) (bit m 4) (PatchFilter.cnb m) o &&
    (twoOrbitStar 35 (x+1,y+1) (bit m 4) (PatchFilter.cnb m) o==0)

/-- Every parent chain exits the rectangle within the allotted budget. -/
def exits (A : Arrows) : Nat → Int → Int → Bool
  | 0, _, _ => false
  | fuel+1, r, c =>
    if r<0 || c<0 || r≥30 || c≥30 then true else
    match (A r.toNat c.toNat).val with
    | 0 => exits A fuel r (c+1)
    | 1 => exits A fuel (r+1) c
    | 2 => exits A fuel r (c-1)
    | _ => exits A fuel (r-1) c

/-- The open rooted bulk crop without the thirteen-mask hypothesis. -/
def RootedCrop (M : Marks) (A : Arrows) : Prop :=
  (∀ r : Fin 30, ∀ c : Fin 29, owns (A r c==0) (A r (c.val+1)==2) (M r c) (M r (c.val+1)) = true) ∧
  (∀ r : Fin 29, ∀ c : Fin 30, owns (A r c==1) (A (r.val+1) c==3) (M r c) (M (r.val+1) c) = true) ∧
  (∀ r c : Fin 28, accepts (5+(r.val+1)%3) (5+(c.val+1)%3) (winMask M r c) = true) ∧
  (∀ r c : Fin 28, priced r c (winMask M r c) (A (r.val+1) (c.val+1)).val = true) ∧
  (∀ j : Fin 10, ∀ i : Fin 9, winMask M (3*j.val) (3*i.val)=73 →
    winMask M (3*j.val) (3*(i.val+1))=73) ∧
  (∀ i : Fin 10, winMask M 0 (3*i.val)=73 ∧
    ∀ a : Fin 3, (A 0 (3*i.val+a.val)==3)=(a==0)) ∧
  (∀ r c : Fin 30, exits A 901 r.val c.val=true)

private theorem verified : RootedCrop M A ∧
    (∀ j : Fin 4, ∀ i : Fin 10, winMask M (3*j.val) (3*i.val)=73) := by
  unfold RootedCrop
  native_decide

/-- Local port ownership, both physical price catalogues, eastward ray
closure, and four plateau rows rooted at the top do not force the
thirteen masks at the `(4,3)` target measured from the last plateau
row. This is not an equality witness on a full square. -/
theorem rooted_crop_not_straight :
    ∃ M A, (RootedCrop M A ∧
      (∀ j : Fin 4, ∀ i : Fin 10, winMask M (3*j.val) (3*i.val)=73)) ∧
      winMask M 21 9=18 ∧ winMask M 21 9 &&& 16 ≠ 0 ∧ winMask M 21 9 &&& 170 ≠ 0 := by
  exact ⟨M,A,verified,by decide,by decide,by decide⟩

/-- A first 73→129 break really does occur at the left read edge of
the rooted open crop, followed immediately by 9 and a plain suffix. -/
theorem rooted_crop_first_break :
    ∃ M A, RootedCrop M A ∧
      (∀ j : Fin 4, ∀ i : Fin 10, winMask M (3*j.val) (3*i.val)=73) ∧
      (∀ i : Fin 10, winMask M 12 (3*i.val)=(if i.val=0 then 129 else if i.val=1 then 9 else 73)) ∧
      winMask M 21 9=18 := by
  exact ⟨M,A,verified.1,verified.2,by native_decide,by decide⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
