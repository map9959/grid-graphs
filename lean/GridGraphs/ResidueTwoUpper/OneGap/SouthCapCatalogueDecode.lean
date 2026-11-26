import GridGraphs.Tests.SouthCapCoveragePhysical
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapInterface
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPhysicalPatch

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero L7 FanSlab
set_option maxRecDepth 1024

private theorem allowed_fit : ∀ r c : Fin 7, (allowedWords (6+r.val) (6+c.val)).all (· < 2^36) := by
  native_decide

private theorem allowed_lt {r c m : Nat} (hr : 6≤r ∧ r≤12) (hc : 6≤c ∧ c≤12)
    (mem : m∈allowedWords r c) : m<2^36 := by
  let i : Fin 7 := ⟨r-6,by omega⟩
  let j : Fin 7 := ⟨c-6,by omega⟩
  have e : 6+i.val=r := by dsimp [i]; omega
  have f : 6+j.val=c := by dsimp [j]; omega
  have h := allowed_fit i j
  rw [e,f] at h
  exact of_decide_eq_true (List.all_eq_true.mp h _ mem)

def FitsWord (w : Word) : Prop := w.1<512 ∧ w.2.1<512 ∧ w.2.2.1<512 ∧ w.2.2.2<512

private theorem extra_fits {r c : Nat} {w : Word} (mem : w∈extra r c) : FitsWord w := by
  unfold extra at mem
  split_ifs at mem <;> simp_all [FitsWord] <;>
    rcases mem with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> decide

private theorem pack_inj {w v : Word} (hw : FitsWord w) (hv : FitsWord v)
    (eq : packWord w=packWord v) : w=v := by
  rcases w with ⟨a,b,c,d⟩
  rcases v with ⟨e,f,g,h⟩
  simp only [packWord,FitsWord] at hw hv eq
  have A : a=e := by omega
  have B : b=f := by omega
  have C : c=g := by omega
  have D : d=h := by omega
  subst e f g h
  rfl

theorem allowed_pack_admitted {r c : Nat} {w : Word} (hr : 6≤r ∧ r≤12) (hc : 6≤c ∧ c≤12)
    (fit : FitsWord w) (mem : packWord w∈allowedWords r c) : widened ordinary r c w := by
  unfold allowedWords at mem
  rcases List.mem_append.mp mem with bank|added
  · left
    have ix : 7*(r-6)+(c-6)<packedBank.size := by rw [packed_bank_size.1]; omega
    refine ⟨hr.1,hr.2,hc.1,hc.2,?_⟩
    simp only [Array.getElem?_eq_getElem ix,Option.any_some]
    rw [getElem!_pos packedBank (7*(r-6)+(c-6)) ix] at bank
    exact Array.contains_iff_mem.mpr (by simpa using bank)
  · obtain ⟨v,hv,eq⟩ := List.mem_map.mp added
    exact .inr ((pack_inj (extra_fits hv) fit eq) ▸ hv)

private theorem packVars_append (a : Nat → Bool) (xs ys : List Nat) :
    packVars a (xs++ys)=packVars a xs+2^xs.length*packVars a ys := by
  induction xs with
  | nil => simp [packVars]
  | cons x xs ih => simp only [List.cons_append,packVars,ih,List.length_cons,pow_succ]; ring

private theorem pack_four (a : Nat → Bool) :
    packVars a fourVars =
      packWord (packVars a (patchVars (6,6)),packVars a (patchVars (6,9)),
        packVars a (patchVars (9,6)),packVars a (patchVars (9,9))) := by
  have len (p : Offset) : (patchVars p).length=9 := by simp [patchVars]
  simp only [fourVars,List.flatMap_cons,List.flatMap_nil,List.append_nil,packVars_append,len,packWord]
  rfl

private theorem matched_word {a : Nat → Bool} {m : Nat} (lt : m<2^36)
    (bits : ∀ z∈fourVars.zipIdx, a z.1=m.testBit z.2) :
    packVars a fourVars=m := by
  have len : fourVars.length=36 := by decide
  have small := packVars_lt a fourVars
  rw [len] at small
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<36
  · have atI : i<fourVars.length := by omega
    rw [packVars_bit _ _ _ atI]
    exact bits (fourVars[i],i) (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem atI))
  · have le : 2^36≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le small le),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le lt le)]

private theorem atlas_base_end : ∀ i : Fin 7, baseAt (6+i.val)+9<117 := by decide

private theorem allowed_patch_here {h w r c : Nat} (hr : r+2≤h) (hc : c+2≤w) (p : Offset)
    (hi : p.1≤9) (hj : p.2≤9) : inside 117 (absAt (endTag h r) (endTag w c) p) := by
  have x := tag_range hr
  have y := tag_range hc
  have R := atlas_base_end ⟨endTag h r-6,by omega⟩
  have C := atlas_base_end ⟨endTag w c-6,by omega⟩
  dsimp only at R C
  rw [show 6+(endTag h r-6)=endTag h r by omega] at R
  rw [show 6+(endTag w c-6)=endTag w c by omega] at C
  simp only [inside,absAt,Bool.and_eq_true]
  refine ⟨⟨⟨decide_eq_true (by omega),decide_eq_true (by omega)⟩,
    decide_eq_true (by omega)⟩,decide_eq_true (by omega)⟩

private theorem square_fits {n : Nat} (F : Finset (GridVertex n n)) (v : View) (r c : Nat) :
    square F v r c<512 := (FanSlab.unpack _).1

def rectWord {n : Nat} (F : Finset (GridVertex n n)) (v : View) (k h w r c : Nat) : Word :=
  let R := firstRow k h+3*r
  let C := firstRow k w+3*c
  (square F v R C,square F v R (C+3),square F v (R+3) C,square F v (R+3) (C+3))

abbrev capWord {n : Nat} (F : Finset (GridVertex n n)) (v : View) (k h r c : Nat) :=
  rectWord F v k h (width h) r c

set_option maxHeartbeats 1000000 in
private theorem physical_four_pack {u k h w r c F v q} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q (fanDirection u v)) :
    packVars (numericField (windowField pl H)) fourVars=packWord (rectWord F v k h w r c) := by
  let a := numericField (windowField pl H)
  change packVars a fourVars=_
  rw [pack_four]
  let R := firstRow k h+3*r
  let C := firstRow k w+3*c
  have wide := pl.wide
  have short := pl.height
  have narrow := pl.width
  have hx (t : Nat) : haloSite k h r (6+t)=R+t := by
    simp only [haloSite,R,firstRow]; omega
  have hy (t : Nat) : haloSite k w c (6+t)=C+t := by
    simp only [haloSite,C,firstRow]; omega
  have read (i j : Nat) (il : i≤3) (jl : j≤3) :
      packVars a (patchVars (6+i,6+j)) = square F v (R+i) (C+j) := by
    have h := physical_patch_square pl H (6+i,6+j) (by dsimp; omega) (by dsimp; omega)
      (allowed_patch_here pl.row pl.col _ (by dsimp; omega) (by dsimp; omega))
    simpa only [hx,hy] using h
  have nw := read 0 0 (by decide) (by decide)
  have ne := read 0 3 (by decide) (by decide)
  have sw := read 3 0 (by decide) (by decide)
  have se := read 3 3 (by decide) (by decide)
  dsimp only [Nat.add_zero] at nw ne sw
  rw [nw,ne,sw,se]
  rfl

/-- The 36 matched bits decode to the four actual tile masks, in the
producer's NW, NE, SW, SE order. This is uniform in the physical side. -/
theorem physical_rectangle_word {u k h w r c F v q} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    : widened ordinary (endTag h r) (endTag w c) (rectWord F v k h w r c) := by
  let a := numericField (windowField pl H)
  obtain ⟨m,mem,bits⟩ := all_physical_windows_bits pl H acy score
  have rtag := tag_range pl.row
  have ctag := tag_range pl.col
  have packed : packVars a fourVars=m := matched_word (allowed_lt rtag ctag mem) bits
  have decoded : packWord (rectWord F v k h w r c)=m :=
    (physical_four_pack pl H).symm.trans packed
  have chosen : packWord (rectWord F v k h w r c)∈allowedWords (endTag h r) (endTag w c) := by
    rw [decoded]; exact mem
  have fit : FitsWord (rectWord F v k h w r c) := ⟨square_fits ..,square_fits ..,square_fits ..,square_fits ..⟩
  exact allowed_pack_admitted rtag ctag fit chosen

theorem physical_catalogue_admitted {u h F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (hk : 59≤11+14*u) (hh : h≤43) :
    OrdinaryCapAdmitted F v (11+14*u) h := by
  intro r c hr hc
  exact physical_rectangle_word ⟨rfl,by omega,by omega,by unfold width; omega,hr,hc⟩ H acy score

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
