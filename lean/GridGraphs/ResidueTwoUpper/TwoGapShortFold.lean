import GridGraphs.ResidueTwoUpper.TwoGapFold

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap

/-- All ordinary aligned exits `2+3*q`, including both near ends. At
side 35 there is no expansion. At every later width one base chart at
side 77 suffices: insertion on both sides is needed only for base q=12. -/
theorem short_cover (u q : Nat) (west : 1≤q) (east : q+2≤11+14*u) :
    (u=0 ∧ 1≤q ∧ q≤9) ∨
    ∃ (p a b : Nat), 1≤p ∧ p≤23 ∧ q=p+a ∧ 11+14*u=25+a+b ∧
      (0<a → 12≤p) ∧ (0<b → p≤12) := by
  by_cases h : u=0
  · left; omega
  right
  let a := min (q-12) (14*(u-1))
  exact ⟨q-a,a,14*(u-1)-a,by dsimp [a]; omega⟩

def shortCol (a b x : Int) := fold 16 b (fold 8 a x)

/-- The base exit must be far enough away only from a *nonzero*
insertion. This matters at near-end charts, where q may be 1 or 23. -/
theorem short_key {a b q i j δ ε : Int} (ha : 0≤a) (hb : 0≤b)
    (left : 0<a → 12≤q) (right : 0<b → q≤12)
    (dx : -4≤δ ∧ δ≤9) (dy : -4≤ε ∧ ε≤9) :
    tileKey (25+a+b) (q+a) i j δ ε=tileKey 25 q (shortCol a b i) (row a b j) δ ε := by
  have ex : clip (exitΔ (q+a) i δ)=clip (exitΔ q (shortCol a b i) δ) := by
    unfold clip exitΔ site shortCol fold
    split_ifs <;> omega
  have f := chart_fold (k:=25+b) (g:=8) (i:=i) (by decide) (by omega) ha dx
  have g := chart_fold (k:=25) (g:=16) (i:=fold 8 a i) (by decide) (by decide) hb dx
  have h := chart_fold (k:=25) (g:=8) (i:=j) (by decide) (by decide) (show 0≤a+b by omega) dy
  have A := ends_fold (k:=25+b) (g:=8) (i:=i) (by decide) (by omega) ha dx
  have B := ends_fold (k:=25) (g:=16) (i:=fold 8 a i) (by decide) (by decide) hb dx
  have C := ends_fold (k:=25) (g:=8) (i:=j) (by decide) (by decide) (show 0≤a+b by omega) dy
  have e1 : 25+b+a=25+a+b := by omega
  have e2 : 25+(a+b)=25+a+b := by omega
  rw [e1] at f A; rw [e2] at h C
  have end0 {k z l w : Int} (h : ∀ v : Int, 0≤v → v≤1 → deep k (z+v)=deep l (w+v)) :
      deep k z=deep l w := by simpa using h 0 (by decide) (by decide)
  simp only [tileKey,shortCol,row,f,g,h,A.1,B.1,C.1,ex,end0 A.2,end0 B.2,end0 C.2,
    A.2 1 (by decide) (by decide),B.2 1 (by decide) (by decide),C.2 1 (by decide) (by decide)]

/-- Canonical `0011` datum at a single site. Out-of-board sites have no
frame literal. Depth one is empty. Direction codes match `outDir`, with
4 for the NW sink and 5 for no prescribed parent. The Boolean at the end
is the ordinary north-tooth implication guard. -/
def rimDatum (k q x y : Int) : Option Bool × Nat × Bool :=
  let l := clip x; let r := clip (3*k+1-x)
  let t := clip y; let b := clip (3*k+1-y)
  let e := clip (x-(2+3*q))
  if min (min t b) (min l r)<0 then (none,5,false) else
  let atTop := t=0; let atBottom := b=0; let atLeft := l=0; let atRight := r=0
  let boundary := atTop ∨ atBottom ∨ atLeft ∨ atRight
  let hole := (atTop ∧ (l=1 ∨ l=2)) ∨ (atRight ∧ (t=1 ∨ t=2)) ∨
    (atBottom ∧ r=1) ∨ (atLeft ∧ b=1)
  let mark := if boundary then some (decide (¬hole)) else
    if t=1 ∨ b=1 ∨ l=1 ∨ r=1 then some false else none
  let parent := if atTop then
      (if atLeft then 4 else if l=1 then 2 else if e<0 then 0 else if e=0 then 1 else 2)
    else if atLeft then 3 else if atBottom then 2 else if atRight then
      (if t=1 then 3 else 1) else 5
  (mark,parent,decide (t=2 ∧ 3≤l ∧ 3≤r ∧ e≠0))

theorem rim_fold {a b q i j δ ε : Int} (ha : 0≤a) (hb : 0≤b)
    (left : 0<a → 12≤q) (right : 0<b → q≤12) (dx : -4≤δ ∧ δ≤9) (dy : -4≤ε ∧ ε≤9) :
    rimDatum (25+a+b) (q+a) (site i δ) (site j ε)=
      rimDatum 25 q (site (shortCol a b i) δ) (site (row a b j) ε) := by
  have eq := short_key ha hb left right (i:=i) (j:=j) dx dy
  have X := congrArg (fun z => z.2.2.1) eq
  have Y := congrArg (fun z => z.2.2.2.1) eq
  have E := congrArg (fun z => z.2.2.2.2.1) eq
  dsimp only [tileKey,nearEnds,Prod.mk.injEq] at X Y
  dsimp only [tileKey,exitΔ] at E
  simp only [Prod.mk.injEq] at X Y
  simp only [rimDatum,X.1,X.2,Y.1,Y.2,E]

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap
