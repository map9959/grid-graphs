import GridGraphs.ResidueTwoUpper.TwoGapRotate
import GridGraphs.ResidueTwoUpper.TwoGapShortFold

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap
open ResidueZero Stencil Words Box

private def rimMark (t b l r : Int) : Option Bool :=
  if min (min t b) (min l r)<0 then none else
  if t=0 ∨ b=0 ∨ l=0 ∨ r=0 then some (decide (¬((t=0 ∧ (l=1 ∨ l=2)) ∨ (r=0 ∧ (t=1 ∨ t=2)) ∨
    (b=0 ∧ r=1) ∨ (l=0 ∧ b=1)))) else if t=1 ∨ b=1 ∨ l=1 ∨ r=1 then some false else none

private theorem markPart (k q x y : Int) : (rimDatum k q x y).1 =
    rimMark (clip y) (clip (3*k+1-y)) (clip x) (clip (3*k+1-x)) := by
  unfold rimDatum rimMark
  dsimp only
  split <;> rfl

private theorem clip_small (x j : Int) (hj : 0≤j ∧ j≤2) : clip x=j ↔ x=j := by unfold clip; omega

private theorem boxed : ∀ (c : Corner) (r k : Fin 5) (flag : Bool),
    rimMark (if c.1 then 4 else r.val) (if c.1 then r.val else 4)
      (if c.2 then 4 else k.val) (if c.2 then k.val else 4)=some flag →
      (r.val≤1 ∨ k.val≤1) ∧ cell c (if c.1 then (if c.2 then 7 else 13) else (if c.2 then 12 else 3)) 0 r k=flag.toNat := by native_decide

private theorem outer {h r k : Int} (rh : 0≤r ∧ r≤h) (kh : 0≤k ∧ k≤h)
    (far : 4<r ∧ r+4<h ∨ 4<k ∧ k+4<h) (b : Bool)
    (known : rimMark (clip r) (clip (h-r)) (clip k) (clip (h-k))=some b) :
    (b=true ∧ min (min r (h-r)) (min k (h-k))=0 ∧ 3 ≤ max (min r (h-r)) (min k (h-k))) ∨
    (b=false ∧ min (min r (h-r)) (min k (h-k))=1) := by
  have nn (z : Int) (hz : 0≤z) : 0≤clip z := by unfold clip; omega
  have z : ¬min (min (clip r) (clip (h-r))) (min (clip k) (clip (h-k)))<0 := by
    have A := nn _ rh.1; have B := nn (h-r) (by omega); have C := nn _ kh.1; have D := nn (h-k) (by omega); omega
  unfold rimMark at known; rw [if_neg z] at known
  simp only [clip_small _ 0 (by decide),clip_small _ 1 (by decide),clip_small _ 2 (by decide)] at known
  split_ifs at known with edge ring
  · left; refine ⟨(Option.some.inj known).symm.trans (decide_eq_true (by omega)),by omega,by omega⟩
  · right; exact ⟨(Option.some.inj known).symm,by omega⟩

set_option maxHeartbeats 700000 in
/-- In the adjacent normalized chart the *physical* two-ring marks
are precisely the marks used by `rimDatum`. No alignment or numerical
value is needed for the exit in this statement. -/
theorem chart_marks {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by omega) F)=code4 0 0 1 1)
    (v : GridVertex (35+42*u) (35+42*u)) (q : Int) (b : Bool)
    (prescribed : (rimDatum (11+14*(u:Int)) q v.2.val v.1.val).1=some b) :
    decide (v∈F)=b := by
  let n := 35+42*u; have hn : 35≤n := by dsimp [n]; omega
  obtain ⟨P,_,step,_,_,_,good,_⟩ := Frame.frame_of_score u F acy score
  have cm := corners_marked u F acy score
  have line (x) := (Frame.star_geometry hn F P step x (good (.inl x))).1
  have emp (x) := (Frame.star_geometry hn F P step x (good (.inl x))).2.1
  have decode : ∀ s : Fin 4 → Fin 4, packed s=code4 0 0 1 1 →
      ∀ i, s i=(if i.val<2 then 0 else 1) := by native_decide
  have words (c : Corner) : physicalWord hn F c=(if c.1 then (if c.2 then 7 else 13) else (if c.2 then 12 else 3)) := by
    have ok := physicalWord_ok hn F P good c
    have d := decode _ canon
    rcases c with ⟨r,k⟩
    cases r <;> cases k
    case' false.false => have h := d 0; change digit hn F (false,false)=0 at h
    case' false.true => have h := d 1; change digit hn F (false,true)=0 at h
    case' true.false => have h := d 3; change digit hn F (true,false)=1 at h
    case' true.true => have h := d 2; change digit hn F (true,true)=1 at h
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ok
    all_goals rcases ok with z|z|z|z <;> first | exact z | simp [digit,z] at h
  have R := v.1.isLt; have K := v.2.isLt
  change v.1.val<n at R; change v.2.val<n at K
  let c : Corner := (decide (v.1.val>4),decide (v.2.val>4))
  by_cases corner : (v.1.val≤4 ∨ v.1.val+5≥n) ∧ (v.2.val≤4 ∨ v.2.val+5≥n)
  · have small (x : Fin n) (near : x.val≤4 ∨ x.val+5≥n) : loc n (decide (x.val>4)) x.val<5 := by
      by_cases far : x.val>4 <;> simp [loc,far] <;> omega
    let r : Fin 5 := ⟨loc n c.1 v.1.val,small _ corner.1⟩
    let k : Fin 5 := ⟨loc n c.2 v.2.val,small _ corner.2⟩
    have same : v=Box.site hn c r k := by
      ext <;> dsimp [Box.site,r,k,c,loc] <;> split_ifs <;> omega
    have V := cell_physical hn F c cm line emp r k
    have field (c : Corner) (r k : Fin 5) (m : Nat) (flag : Bool)
        (h : (rimDatum (11+14*(u:Int)) q (Box.site hn c r k).2.val (Box.site hn c r k).1.val).1=some flag) :
        cell c (if c.1 then (if c.2 then 7 else 13) else (if c.2 then 12 else 3)) m r k=flag.toNat := by
      have R := r.isLt; have K := k.isLt
      have l (f : Bool) (j : Fin 5) :
          clip ((loc n f j.val:Int))=(if f then 4 else (j.val:Int)) ∧
          clip (3*(11+14*(u:Int))+1-(loc n f j.val:Int))=(if f then (j.val:Int) else 4) := by
        have J := j.isLt; cases f <;> dsimp [clip,n,loc] <;> omega
      rw [markPart] at h
      dsimp only [Box.site] at h
      rw [(l _ _).1,(l _ _).2,(l _ _).1,(l _ _).2] at h
      obtain ⟨near,eq⟩ := boxed c r k flag h
      convert eq using 1; unfold cell; split_ifs <;> omega
    have ph := field c r k (maskAt F (origin (by omega) c 2 2)) b (same ▸ prescribed)
    rw [words] at V
    rw [same]; exact (by decide : Function.Injective Bool.toNat) (V.symm.trans ph)
  · rw [markPart] at prescribed
    let h := 3*(11+14*(u:Int))+1
    have H : h=(n:Int)-1 := by dsimp [h,n]; ring
    have far : 4<(v.1.val:Int) ∧ v.1.val+4<h ∨ 4<(v.2.val:Int) ∧ v.2.val+4<h := by rw [H]; omega
    have T := outer (h:=h) (r:=v.1.val) (k:=v.2.val) (by rw [H]; omega) (by rw [H]; omega) far b prescribed
    rw [H] at T
    obtain ⟨rfl,h1,h2⟩|⟨rfl,h1⟩ := T
    · exact decide_eq_true (line v ⟨h1,h2⟩)
    · simp [emp v h1]

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap
