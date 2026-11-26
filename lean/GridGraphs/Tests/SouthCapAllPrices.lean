import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPriceClauses

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil

def cubeData : Array (List Nat) :=
  (((include_str "../ResidueTwoUpper/OneGap/SouthCapPriceCubes.txt").splitOn "\n").filter
    (!·.isEmpty)).toArray.map fun row =>
      ((row.splitOn " ").filterMap String.toNat?).filterMap fun z =>
        if z=0 then none else some (z-1)

def rejects (row : List Nat) (v : Nat) : Bool :=
  row.any fun z => (v &&& (z%512)) == z/512

def patchReps : List Nat := [6,7,8,15,16,17,18,19,20]
def starReps : List Nat := [6,7,8,17,18,19,20,21,22]
def pricePoint (rs : List Nat) (i j : Nat) : Pos := (rs[i]!,rs[j]!)
def patchCubes (i j : Nat) := cubeData[9*i+j]!
def starCubes (i j o : Nat) := cubeData[81+5*(9*i+j)+o]!
def compass (p : Pos) := (List.range 4).filter fun d => inside 23 (shift p d)
def neighbourCode (ds : List Nat) (m : Nat) :=
  (ds.zipIdx.map fun (d,i) => bit m (i+1) <<< d).sum

def starReject (p : Pos) (ds : List Nat) (o m : Nat) : Bool :=
  let f := bit m 0
  let nb := neighbourCode ds m
  let root := p.1==22 && p.2==22
  !(starOK 23 p f nb o &&
    (if root then f==1 && o==4 else o != 4 || (f==0 && nb==0))) ||
    twoOrbitStar 23 p f nb o != 0

def auditPatch (i j : Nat) : Bool :=
  let p := pricePoint patchReps i j
  let row := patchCubes i j
  (List.range 512).all fun m =>
    rejects row m == (!maskOK m || twoOrbitPatch 23 p m != 0)

def auditStar (i j o : Nat) : Bool :=
  let p := pricePoint starReps i j
  let ds := compass p
  let row := starCubes i j o
  if o≠4 ∧ o∉ds then row.isEmpty else
  (List.range (2^(ds.length+1))).all fun m =>
    rejects row m == starReject p ds o m

theorem checked_all_patches : ∀ i j : Fin 9, auditPatch i j := by native_decide
theorem checked_all_stars : ∀ (i j : Fin 9) (o : Fin 5), auditStar i j o := by native_decide

private theorem patch_rep_finite : ∀ x : Fin 29, ∃ i : Fin 9,
    ResidueZero.rep 21 32 (88+x.val : Nat) = (patchReps[i.val]! : Int) := by decide +kernel
private theorem star_rep_finite : ∀ x : Fin 31, ∃ i : Fin 9,
    ResidueZero.rep 23 32 (88+x.val : Nat) = (starReps[i.val]! : Int) := by decide +kernel

/-- Every atlas point in any of the 49 windows is in the audited
southeast envelope. The output includes clipped sites; callers impose
the appropriate board or patch-origin bound before selecting a row. -/
theorem atlasSite_ge88 {extent i d : Nat} (hi : i+2≤extent) :
    88≤atlasSite extent i d := by
  unfold atlasSite endTag repTile; split_ifs <;> omega

theorem atlas_patch_rep {x : Nat} (lo : 88≤x) (hi : x<117) :
    ∃ i : Fin 9, ResidueZero.rep 21 32 x=(patchReps[i.val]! : Int) := by
  obtain ⟨i,h⟩ := patch_rep_finite ⟨x-88,by omega⟩
  refine ⟨i,?_⟩
  simpa only [show 88+(x-88)=x by omega] using (show
    ResidueZero.rep 21 32 (88+(x-88):Nat)=(patchReps[i.val]! : Int) from h)

theorem atlas_star_rep {x : Nat} (lo : 88≤x) (hi : x<119) :
    ∃ i : Fin 9, ResidueZero.rep 23 32 x=(starReps[i.val]! : Int) := by
  obtain ⟨i,h⟩ := star_rep_finite ⟨x-88,by omega⟩
  refine ⟨i,?_⟩
  simpa only [show 88+(x-88)=x by omega] using (show
    ResidueZero.rep 23 32 (88+(x-88):Nat)=(starReps[i.val]! : Int) from h)

private theorem atlasPatch_location (p : Pos) (m : Nat) :
    twoOrbitPatch 119 p m = twoOrbitPatch 23 (representative 21 32 p) m := by
  have h (g : Nat) := patchLocation_transport (b:=21) (j:=32) (by decide) (by decide) p g
  norm_num at h
  simp only [twoOrbitPatch,show (119:Int)-2=117 by decide,show (23:Int)-2=21 by decide,h]

private theorem atlasStar_location (p : Pos) (f nb o : Nat) :
    twoOrbitStar 119 p f nb o = twoOrbitStar 23 (representative 23 32 p) f nb o := by
  have h (g : Nat) := starLocation_transport (b:=23) (j:=32) (by decide) (by decide) p g
  norm_num at h
  simp only [twoOrbitStar,h]

/-- All patch origins (including every clipped southeast halo) can
reuse the finite replay at the representative of their actual site. -/
theorem atlas_patch_reject {p : Pos} (i j : Fin 9)
    (rep : representative 21 32 p=pricePoint patchReps i j) {m : Nat} (hm : m<512) :
    rejects (patchCubes i j) m = (!maskOK m || twoOrbitPatch 119 p m != 0) := by
  have replay := List.all_eq_true.mp (checked_all_patches i j) m (List.mem_range.mpr hm)
  rw [atlasPatch_location,rep]
  exact beq_iff_eq.mp replay

def starReject119 (p : Pos) (ds : List Nat) (o m : Nat) : Bool :=
  let f := bit m 0
  let nb := neighbourCode ds m
  let root := p.1==118 && p.2==118
  !(starOK 119 p f nb o &&
    (if root then f==1 && o==4 else o != 4 || (f==0 && nb==0))) ||
    twoOrbitStar 119 p f nb o != 0

/-- Transport the checked star cubes with their original bit order.
The predicate agrees with the producer for both the fixed corner
sink and every permitted nonroot direction. -/
theorem atlas_star_reject {p : Pos} (i j : Fin 9) (o : Fin 5)
    (rep : representative 23 32 p=pricePoint starReps i j)
    (possible : o.val=4 ∨ o.val∈compass (pricePoint starReps i j))
    {m : Nat} (hm : m<2^((compass (pricePoint starReps i j)).length+1)) :
    rejects (starCubes i j o) m =
      starReject119 p (compass (pricePoint starReps i j)) o m := by
  have no : ¬(o.val≠4 ∧ o.val∉compass (pricePoint starReps i j)) := by tauto
  have ok := checked_all_stars i j o
  unfold auditStar at ok
  rw [if_neg no] at ok
  have replay := beq_iff_eq.mp (List.all_eq_true.mp ok m (List.mem_range.mpr hm))
  rw [replay]
  have loc d := congrArg (fun l : StarLocation => (l.neighbour d).isSome)
    (starLocation_transport (b:=23) (j:=32) (by decide) (by decide) p 0)
  have insideEq (d : Nat) :
      inside 119 (shift p d)=inside 23 (shift (pricePoint starReps i j) d) := by
    have h := loc d
    norm_num [image,rep,starLocation,located] at h
    split_ifs at h <;> simp_all
  have tail (x : Int) : (ResidueZero.rep 23 32 x==22)=(x==118) := by
    unfold ResidueZero.rep; split_ifs <;> apply Bool.eq_iff_iff.mpr <;>
      simp only [beq_iff_eq] <;> omega
  have sr : ((pricePoint starReps i j).1==22 && (pricePoint starReps i j).2==22) =
      (p.1==118 && p.2==118) := by
    rw [←rep]; simp only [representative,tail]
  simp only [starReject,starReject119,sr,atlasStar_location,rep,starOK,insideEq]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
