import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPhysicalPatch

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil Std.Sat

private theorem starIndexCheck : ∀ x : Fin 31,
    let y : Int := ((88+x.val : Nat) : Int)
    starIx y < 9 ∧ rep 23 32 y=(starReps[starIx y]! : Int) := by decide +kernel

private theorem starIndex {x : Nat} (lo : 88≤x) (hi : x<119) :
    starIx x < 9 ∧ rep 23 32 x=(starReps[starIx x]! : Int) := by
  have h := starIndexCheck ⟨x-88,by omega⟩
  dsimp only at h
  rwa [show 88+(x-88)=x by omega] at h

private theorem starCompassCheck : ∀ x y : Fin 31,
    let X : Int := ((88+x.val : Nat) : Int)
    let Y : Int := ((88+y.val : Nat) : Int)
    (List.range 4).filter (fun d => inside 119 (shift (X,Y) d)) =
      compass (pricePoint starReps (starIx X) (starIx Y)) := by native_decide

private theorem starCompass {x y : Nat} (lx : 88≤x) (ly : 88≤y) (hx : x<119) (hy : y<119) :
    (List.range 4).filter (fun d => inside 119 (shift (x,y) d)) =
      compass (pricePoint starReps (starIx x) (starIx y)) := by
  have h := starCompassCheck ⟨x-88,by omega⟩ ⟨y-88,by omega⟩
  dsimp only at h
  rwa [show 88+(x-88)=x by omega,show 88+(y-88)=y by omega] at h

/-- A star whose guard is active only needs to pass the local producer
predicate. The audited cube row then gives exactly the CNF law, with
its on-board compass list and the generator's own numbering. -/
theorem atlas_star_row_law {h w r c : Nat} (hr : r+2≤h) (hc : c+2≤w)
    (p : Offset) (a : Nat → Bool) (board : onBoard (endTag h r) (endTag w c) p)
    (o : Nat) :
    let z := absAt (endTag h r) (endTag w c) p
    let ds := (List.range 4).filter fun d => inside 119 (shift z d)
    let vs := markVar p :: ds.map (fun d => markVar (move p d))
    let guard : CNF.Clause Nat := if o=4 then (ds.map (arcVar p)).map (·,true) else [(arcVar p o,false)]
    let row := starCubes (starIx z.1) (starIx z.2) o
    o∈ds++[4] →
    (guard.eval a≠true → starReject119 z ds o (packVars a vs)=false) →
    (guard.eval a=true ∨ rejects row (packVars a vs)=false) ∧
      (∀ b∈row, b%512<2^vs.length ∧ (b/512 &&& b%512)=b/512) := by
  dsimp only
  let X := atlasSite h r p.1
  let Y := atlasSite w c p.2
  have xy : absAt (endTag h r) (endTag w c) p = ((X:Int),(Y:Int)) := by
    simp only [X,Y,absAt,baseAt,atlasSite,Nat.cast_add]
  obtain ⟨hx,hy⟩ := (onBoard_iff p).mp board
  have lx : 88≤X := atlasSite_ge88 hr
  have ly : 88≤Y := atlasSite_ge88 hc
  have ix := starIndex lx hx
  have iy := starIndex ly hy
  let i : Fin 9 := ⟨starIx X,ix.1⟩
  let j : Fin 9 := ⟨starIx Y,iy.1⟩
  have rp : representative 23 32 ((X:Int),(Y:Int))=pricePoint starReps i j :=
    Prod.ext ix.2 iy.2
  let ds := compass (pricePoint starReps i j)
  have dsEq : (List.range 4).filter (fun d => inside 119 (shift ((X:Int),(Y:Int)) d))=ds :=
    starCompass lx ly hx hy
  rw [xy,dsEq]
  intro mem sound
  have poss : o=4 ∨ o∈ds := by simpa [or_comm] using mem
  have small : o<5 := by
    rcases poss with rfl|mem
    · decide
    · exact Nat.lt_trans (List.mem_range.mp (List.mem_filter.mp mem).1) (by decide)
  let d : Fin 5 := ⟨o,small⟩
  have lt := packVars_lt a (markVar p :: ds.map (fun d => markVar (move p d)))
  simp only [List.length_cons,List.length_map] at lt
  constructor
  · by_cases yes : (if o=4 then (ds.map (arcVar p)).map (·,true)
        else [(arcVar p o,false)] : CNF.Clause Nat).eval a=true
    · exact Or.inl yes
    · exact Or.inr ((atlas_star_reject i j d rp poss lt).trans (sound yes))
  · intro b hb
    simp only [List.length_cons,List.length_map]
    exact star_cube_shape i j d b hb

def StarReadout (r c : Nat) (a : Nat → Bool) : Prop :=
  ∀ p∈sites, onBoard r c p →
    let z := absAt r c p
    let ds := (List.range 4).filter fun d => inside 119 (shift z d)
    ds.all (inHalo p) → ∀ o∈ds++[4],
    let vs := markVar p :: ds.map (fun d => markVar (move p d))
    let guard : CNF.Clause Nat := if o=4 then (ds.map (arcVar p)).map (·,true) else [(arcVar p o,false)]
    guard.eval a≠true → starReject119 z ds o (packVars a vs)=false

/-- The two physical readouts, before any cube lookup:
the nine marks must form an admissible zero-price patch, and the
guarded compass readout must be an admissible zero-price star. -/
structure PriceReadoutLaws (r c : Nat) (a : Nat → Bool) : Prop where
  patch : ∀ p∈sites, onBoard r c p →
    (p.1+2<18 && p.2+2<18 && inside 117 (absAt r c p)) →
    maskOK (packVars a (patchVars p)) ∧
      twoOrbitPatch 119 (absAt r c p) (packVars a (patchVars p))=0
  star : StarReadout r c a

theorem physical_price_readout_of_stars {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (acy : (Bonds F).IsAcyclic)
    (star : StarReadout (endTag h r) (endTag w c) (numericField (windowField pl H))) :
    PriceReadoutLaws (endTag h r) (endTag w c) (numericField (windowField pl H)) where
  patch p _ _ valid := by
    simp only [Bool.and_eq_true,decide_eq_true_eq] at valid
    exact physical_patch_readout pl H acy p valid.1.1 valid.1.2 valid.2
  star := star

/-- No physical rim premise and no cube-shape premise remain. -/
theorem physical_mark_price_laws {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir)
    (readout : PriceReadoutLaws (endTag h r) (endTag w c) (numericField (windowField pl H))) :
    MarkPriceLaws (endTag h r) (endTag w c) H.cornerBit (numericField (windowField pl H)) where
  rim := physical_rim_law pl H
  patch p hp hb valid := by
    have h := readout.patch p hp hb valid
    simp only [Bool.and_eq_true] at valid
    exact atlas_patch_row_law pl.row pl.col p _ valid.2 h.1 h.2
  star p hp hb halo o mem :=
    atlas_star_row_law pl.row pl.col p _ hb o mem (readout.star p hp hb halo o mem)

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
