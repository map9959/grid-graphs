import GridGraphs.ResidueTwoUpper.OneGap.ShortPhysical

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero Stencil L7

/-- More than six sites from both walls, the mark and arrow tables are
periodic with period three. Only 17×17 labels are needed, regardless of
the side length. The larger and smaller boards still have their own
physical rows and columns. -/
def tag (u i : Nat) :=
  if i<7 then i else if 26+42*u ≤ i then i-42*u else 7+(i-7)%3

private theorem tag_bound (u i) (hi : i<33+42*u) :
    tag u i<33 ∧ (tag u i<10 ∨ tag u i≥26) := by
  unfold tag; split_ifs <;> omega

private theorem rep_tag (u i t : Nat) (ht : t≤1) :
    rep (21+2*(t:Int)) (4+14*(u:Int)) (i+t:Nat)=rep (21+2*(t:Int)) 4 (tag u i+t:Nat) := by
  unfold rep tag; split_ifs <;> push_cast <;> omega

private theorem table_eq (u r c m f nb o : Nat) :
    twoOrbitPatch (35+42*(u:Int)) (r,c) m=twoOrbitPatch 35 (tag u r,tag u c) m ∧
    twoOrbitStar (35+42*(u:Int)) (center r c) f nb o=twoOrbitStar 35 (center (tag u r) (tag u c)) f nb o := by
  have p : representative 21 (4+14*(u:Int)) ((r:Int),(c:Int))=
      representative 21 4 ((tag u r:Int),(tag u c:Int)) := by
    exact Prod.ext (by simpa [representative] using rep_tag u r 0 (by decide))
      (by simpa [representative] using rep_tag u c 0 (by decide))
  have s : representative 23 (4+14*(u:Int)) (center r c)=
      representative 23 4 (center (tag u r) (tag u c)) := by
    exact Prod.ext (by simpa [center,representative] using rep_tag u r 1 (by decide))
      (by simpa [center,representative] using rep_tag u c 1 (by decide))
  have n : 35+42*(u:Int)=23+3*(4+14*(u:Int)) := by ring
  have a : 35+42*(u:Int)-2=21+3*(4+14*(u:Int)) := by ring
  have pp := patchLocation_transport (b:=21) (by decide) (j:=4) (by decide)
  have ss := starLocation_transport (b:=23) (by decide) (j:=4) (by decide)
  norm_num1 at pp ss
  constructor
  · simp only [twoOrbitPatch,a,patchLocation_transport (b:=21) (by decide) (j:=4+14*(u:Int)) (by positivity),
      show (35:Int)-2=33 by decide,pp,p]
  · simp only [twoOrbitStar,n,starLocation_transport (b:=23) (by decide) (j:=4+14*(u:Int)) (by positivity),ss,s]

private theorem star_tag (u r c : Nat) (hr : r<33+42*u) (hc : c<33+42*u) (f b o : Nat) :
    starPrice (35+42*u) r c f b o=starPrice 35 (tag u r) (tag u c) f b o := by
  have rt := (tag_bound u r hr).1; have ct := (tag_bound u c hc).1
  have ins (n r c : Nat) (hr : r<n-2) (hc : c<n-2) (d : Nat) : inside n (shift (center r c) d) := by
    unfold shift; split <;> simp [center,inside] <;> grind
  simp only [starPrice,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,(table_eq u r c 0 f b o).2,starOK]
  have N : ((35+42*u:Nat):Int)=35+42*(u:Int) := by push_cast; rfl
  have E (d) : inside (35+42*(u:Int)) (shift (center r c) d)=true := N ▸ ins _ r c (by omega : r<35+42*u-2) (by omega) d
  have D (d) : inside 35 (shift (center (tag u r) (tag u c)) d)=true := ins 35 _ _ rt ct d
  simp only [E,D]

def raw (n r c : Nat) : List Label :=
  let stars := Vector.ofFn fun (f : Fin 2) => Vector.ofFn fun (b : Fin 16) =>
    (List.range 5).filter fun o => starPrice n r c f b o
  ((List.range 512).filter (patchPrice n r c)).flatMap fun m =>
    (stars[bit m 4 % 2][PatchFilter.cnb m % 16]).map (m,·)

private theorem raw_tag (u r c : Nat) (hr : r<33+42*u) (hc : c<33+42*u) :
    raw (35+42*u) r c=raw 35 (tag u r) (tag u c) := by
  have patch : patchPrice (35+42*u) r c=patchPrice 35 (tag u r) (tag u c) := by
    funext m; simp only [patchPrice,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,(table_eq u r c m 0 0 0).1]
  simp only [raw,patch,star_tag u r c hr hc]

def chart : Board := build 33 fun r c =>
  if (r<10 ∨ 26≤r) ∧ (c<10 ∨ 26≤c) then raw 35 r c else []
def cached (u : Nat) (T : Board) : Board :=
  build (33+42*u) fun r c => (atRC T (tag u r) (tag u c)).filter fun z =>
    frameOK (35+42*u) r c z.1 && wallOK (35+42*u) r c z.1 z.2

theorem cached_eq (u : Nat) : cached u chart=localBoard (35+42*u) := by
  unfold cached localBoard
  rw [show 35+42*u-2=33+42*u by omega]
  unfold build
  apply congrArg Array.ofFn; funext r
  apply congrArg Array.ofFn; funext c
  have R := tag_bound u r r.isLt; have C := tag_bound u c c.isLt
  simp only [chart,at_build R.1 C.1,R.2,C.2,true_and,if_true,←raw_tag u r c r.isLt c.isLt]
  unfold raw localDomain
  rw [List.filter_flatMap]; simp only [List.filter_map]
  simp only [Function.comp_def]
  induction (List.range 512) with
  | nil => rfl
  | cons a as ih =>
    cases p : patchPrice (35+42*u) r c a <;> cases f : frameOK (35+42*u) r c a <;>
      simp [p,f,List.flatMap_cons,List.filter_cons] at ih ⊢ <;> exact ih
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
