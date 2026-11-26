import GridGraphs.ResidueTwoUpper.TwoGapNorthOwners

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North
open Scan ResidueZero Stencil Words BoundarySix.Connected

/-- Every NW-rooted 0011 chart has the required ordinary exit phase.
The only forest exclusion in the scan is the length-fourteen cycle
around the north 5×4 rectangle. -/
theorem aligned {u d} {F : Finset (GridVertex (35+42*u) (35+42*u))} {P}
    (C : Chart F P d) (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by omega) F)=code4 0 0 1 1) : d%3=2 := by
  classical
  by_contra bad
  let state (j : Nat) : State := (X F (j-2:Int),X F (j-1:Int),X F j,west P j)
  apply no_trace u state
  · have w : west P 0=0 := by
      have E : (fun r : Fin 6 => arrow P r 0==2)=fun _ => false := by
        funext r
        let x := vertex r 0 (n:=35+42*u) (by have := r.isLt; omega) (by omega)
        have no : outDir x (P x)≠2 := by
          unfold outDir
          have nn : ¬(P x).2<x.2 := by change ¬(P x).2.val<0; omega
          rw [if_neg nn]; split_ifs <;> decide
        change (arrow P r 0==2)=false
        have hd : arrow P r 0=outDir x (P x) := by unfold arrow; rw [dif_pos ⟨by have := r.isLt; omega,by omega⟩]
        simp [hd,no]
      unfold west; rw [E]; decide
    have opt := columnOK F acy score canon (j:=0) (i:=0) (by omega) le_rfl (by omega)
    change X F 0∈opts[0]! at opt
    change _∈(opts[0]!).map _
    exact List.mem_map.mpr ⟨_,opt,by simp [state,w,X_off F (j:= -1) (Or.inl (by decide)),X_off F (j:= -2) (Or.inl (by decide))]⟩
  · intro j hj
    let t := X F (j-2:Int); let a := X F (j-1:Int); let b := X F j; let c := X F (j+1:Int)
    have endj : tag u j=34 ↔ j+1=35+42*u := by unfold tag; split_ifs <;> omega
    have opt : c∈(if tag u j==34 then [0] else opts[tag u j+1]!) := by
      by_cases last : j+1=35+42*u
      · have off : c=0 := X_off F (Or.inr (by omega)); simp [endj.mpr last,off]
      · have yes := columnOK F acy score canon (j:=j+1) (i:=j) (by omega) (by omega) le_rfl
        simpa [mt endj.mp last,c] using yes
    have pp := patch_pass C acy hj
    have keep : (!patchPass (tag u j) a b c || (tag u j != 34 && beltFull t a b c))=false := by
      by_cases last : j+1=35+42*u
      · simp [endj.mpr last,patchPass]
      · simp [pp,no_belt F acy (j:=j) (by omega) (by omega),t,a,b,c]
    have ow := owner_pass C acy score bad hj
    change state (j+1)∈(if tag u j==34 then [0] else opts[tag u j+1]!).flatMap _
    apply List.mem_flatMap.mpr; refine ⟨c,opt,?_⟩
    change _∈(if !patchPass (tag u j) a b c || (tag u j != 34 && beltFull t a b c) then [] else _)
    rw [if_neg (by simp [keep])]
    apply List.mem_map.mpr; exact ⟨_,ow,by simp [state,a,b,c]; congr 1 <;> ring⟩

theorem physical_inputs {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (canon : packed (signature (by omega) F)=code4 0 0 1 1) :
    ∃ P q, 1≤q ∧ q+2≤11+14*u ∧ Chart F P (2+3*q) ∧
      (∀ v, IsGridBoundary v → outDir v (P v)=(rimDatum (11+14*(u:Int)) q v.2.val v.1.val).2.1) ∧
      ∀ c : Fin (35+42*u), 3≤c.val ∧ c.val+3≤34+42*u → c.val≠2+3*q →
        ((⟨2,by omega⟩,c) : GridVertex (35+42*u) (35+42*u))∈F → P (⟨2,by omega⟩,c)=(⟨1,by omega⟩,c) :=
  short_inputs F acy score two canon (fun _ _ C => aligned C acy score canon)

/-- Direct handoff to the 35/77 folded catalogues. The same orientation
and column index serve the cost, mark, perimeter and tooth constraints. -/
theorem short_fold_chart {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (canon : packed (signature (by omega) F)=code4 0 0 1 1) :
    ∃ P q, Chart F P (2+3*q) ∧
      ((u=0 ∧ 1≤q ∧ q≤9) ∨ ∃ p a b : Nat, 1≤p ∧ p≤23 ∧ q=p+a ∧
        11+14*u=25+a+b ∧ (0<a → 12≤p) ∧ (0<b → p≤12)) ∧
      (∀ v b, (rimDatum (11+14*(u:Int)) q v.2.val v.1.val).1=some b → decide (v∈F)=b) ∧
      (∀ v, IsGridBoundary v → outDir v (P v)=(rimDatum (11+14*(u:Int)) q v.2.val v.1.val).2.1) ∧
      ∀ c : Fin (35+42*u), 3≤c.val ∧ c.val+3≤34+42*u → c.val≠2+3*q →
        ((⟨2,by omega⟩,c) : GridVertex (35+42*u) (35+42*u))∈F → P (⟨2,by omega⟩,c)=(⟨1,by omega⟩,c) := by
  obtain ⟨P,q,west,east,C,par,tooth⟩ := physical_inputs F acy score two canon
  exact ⟨P,q,C,short_cover u q west east,fun v b => chart_marks F acy score canon v q b,par,tooth⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.North
