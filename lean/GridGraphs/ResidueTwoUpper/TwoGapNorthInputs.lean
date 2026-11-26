import GridGraphs.ResidueTwoUpper.TwoGapNorth

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North
open ResidueZero Stencil Words

private theorem eastWest {h d : Nat} (hd : 3≤d ∧ d<h) (p : Pt)
    (inb : p.1≤h ∧ p.2≤h) (bd : rim h p) :
    (if p=parent h d p then 4 else if p.2<(parent h d p).2 then 0 else
       if p.1<(parent h d p).1 then 1 else if (parent h d p).2<p.2 then 2 else 3) =
    if p.1=0 then (if p.2=0 then 4 else if p.2=1 then 2 else if p.2<d then 0 else if p.2=d then 1 else 2)
    else if p.2=0 then 3 else if p.1=h then 2 else if p.1=1 then 3 else 1 := by
  rcases p with ⟨r,c⟩; unfold rim at bd; dsimp at inb bd; unfold parent
  dsimp; split_ifs <;> simp only [Prod.mk.injEq] at * <;> norm_num at * <;> omega

/-- Exact direction field used to construct the canonical perimeter clauses
in the folded checker. Its only additional premise is the exit phase. -/
theorem parent_field {u d q : Nat} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (chart : Chart F P d) (phase : d=2+3*q) (x : GridVertex (35+42*u) (35+42*u))
    (bd : IsGridBoundary x) :
    outDir x (P x)=(rimDatum (11+14*(u:Int)) q x.2.val x.1.val).2.1 := by
  let h := 34+42*u
  have R := x.1.isLt; have C := x.2.isLt
  have sz : 35+42*u-1=h := by dsimp [h]; omega
  have b := (rim_iff x).mp bd; rw [sz] at b
  have par := chart.perimeter x bd
  have dir : outDir x (P x)=
      (if rc x=rc (P x) then 4 else if (rc x).2<(rc (P x)).2 then 0 else
        if (rc x).1<(rc (P x)).1 then 1 else if (rc (P x)).2<(rc x).2 then 2 else 3) := by
    by_cases same : x=P x
    · rw [←same]; simp [outDir]
    · rw [if_neg (show rc x≠rc (P x) from fun e => same (rc_inj e))]; unfold outDir; rw [if_neg same]; rfl
  change rc (P x)=parent h d (rc x) at par
  rw [par] at dir; rw [dir,eastWest (h:=h) ⟨chart.ordinary.1,chart.ordinary.2.1⟩ _ (by dsimp [h,rc]; omega) b]
  have plus : 3*(11+14*(u:Int))+1=(h:Int) := by dsimp [h]; push_cast; ring
  have D : 2+3*(q:Int)=(d:Int) := by exact_mod_cast phase.symm
  have nn (z : Int) (hz : 0≤z) : 0≤clip z := by unfold clip; omega
  have small (z j : Int) (hj : 0≤j ∧ j≤1) : clip z=j ↔ z=j := by unfold clip; omega
  have neg (z : Int) : clip z<0 ↔ z<0 := by unfold clip; omega
  have valid : ¬ min (min (clip (x.1.val:Int)) (clip ((h:Int)-x.1.val)))
      (min (clip x.2.val) (clip ((h:Int)-x.2.val)))<0 := by
    have := nn _ (Int.natCast_nonneg x.1.val); have := nn _ (Int.natCast_nonneg x.2.val)
    have := nn ((h:Int)-x.1.val) (by dsimp [h]; omega); have := nn ((h:Int)-x.2.val) (by dsimp [h]; omega); omega
  unfold rimDatum; dsimp only; rw [plus,D,if_neg valid]; dsimp only [rc]
  simp only [small _ 0 (by decide),small _ 1 (by decide),neg]
  have R0 : ((x.1.val:Int)=0) ↔ x.1.val=0 := by omega
  have C0 : ((x.2.val:Int)=0) ↔ x.2.val=0 := by omega
  have R1 : ((x.1.val:Int)=1) ↔ x.1.val=1 := by omega
  have C1 : ((x.2.val:Int)=1) ↔ x.2.val=1 := by omega
  have U : (h:Int)-x.1.val=0 ↔ x.1.val=h := by omega
  have V : (h:Int)-x.2.val=0 ↔ x.2.val=h := by omega
  have S : (x.2.val:Int)-d<0 ↔ x.2.val<d := by omega
  have T : (x.2.val:Int)-d=0 ↔ x.2.val=d := by omega
  simp only [R0,C0,R1,C1,U,V,S,T]; unfold rim at b; dsimp [rc] at b
  by_cases r : x.1.val=0 <;> by_cases c : x.2.val=0 <;> by_cases bot : x.1.val=h <;> by_cases right : x.2.val=h <;> simp only [r,c,bot,right,if_true,if_false,ite_true,ite_false] <;> first | rfl | omega

/-- The additional ordinary-tooth clauses in `two_gap_mask_tables.local`:
every marked non-exit north tooth points out of the crop. -/
theorem tooth_arrow {u d : Nat} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (chart : Chart F P d) (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by omega) F)=code4 0 0 1 1)
    (c : Fin (35+42*u)) (bounds : 3≤c.val ∧ c.val+3≤34+42*u) (notExit : c.val≠d)
    (mark : ((⟨2,by omega⟩,c) : GridVertex (35+42*u) (35+42*u))∈F) :
    P (⟨2,by omega⟩,c)=(⟨1,by omega⟩,c) := by
  let atR (i : Fin 3) : GridVertex (35+42*u) (35+42*u) := (⟨i.val,by omega⟩,c)
  have bd : IsGridBoundary (atR 0) := Or.inl rfl
  have top : atR 0∈F := (marked_iff F acy score canon _ bd).mpr (by
    dsimp [hole,rc,atR]; omega)
  have ne : P (atR 0)≠atR 1 := by
    intro bad; have h := chart.perimeter (atR 0) bd
    rw [bad] at h; dsimp [rc,atR,parent] at h; split_ifs at h <;> simp_all [Prod.mk.injEq] <;> omega
  have first : (Bonds F).Adj (atR 1) (atR 0) := ⟨Or.inr ⟨rfl,Or.inr rfl⟩,Or.inr top⟩
  have link := (chart.arrows _ _ first).mpr ne
  have second : (Bonds F).Adj (atR 2) (atR 1) := ⟨Or.inr ⟨rfl,Or.inr rfl⟩,Or.inl mark⟩
  apply (chart.arrows _ _ second).mpr; rw [link]; intro eq
  have := congrArg (fun x : GridVertex (35+42*u) (35+42*u) => x.1.val) eq
  change (0:Nat)=2 at this; contradiction

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North
