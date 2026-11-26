import GridGraphs.ResidueTwoUpper.TwoGapPhysicalBox

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
open ResidueZero Stencil Words BoundarySix.Connected

def fringe (p : Pos) := -6≤p.1 ∧ p.1≤11 ∧ -6≤p.2 ∧ p.2≤11
private theorem wide {p} (h : halo p) : fringe p := by unfold halo at h; unfold fringe; omega
private theorem wide_shift {p} (h : halo p) (d : Fin 4) : fringe (shift p d) := by
  unfold halo at h; fin_cases d <;> norm_num [fringe,shift] <;> omega
private theorem wide_base {p} (h : halo p) (v : Bool) : fringe (edgeBase p v) := by
  unfold halo at h; cases v <;> dsimp [fringe,edgeBase] <;> omega
private theorem wide_off {p} (h : halo p) (b : Fin 9) : fringe (plus3 p b) := by
  unfold halo at h; have := b.isLt; dsimp [fringe,plus3,offset]; omega

theorem local_congr {s t : Pos → Stamp} {l : Field} (eq : ∀ p, fringe p → s p=t p)
    (L : Local s l) : Local t l := by
  have sw {p} (h : halo p) : core t p → core s p := by simp only [core,onB,eq _ (wide h)]; exact id
  constructor
  · intro p hp; simpa only [onB,eq p (wide hp)] using L.off p hp
  · intro p hp; simpa only [rimAt,eq p (wide hp.1)] using L.rim p (sw hp.1 hp)
  · intro p hp; simpa only [rimAt,eq p (wide hp.1)] using L.parents p (sw hp.1 hp)
  · intro p hp; simpa only [starPos,eq p (wide hp.1)] using L.corner p (sw hp.1 hp)
  · intro p hp; simpa only [rimAt,eq p (wide hp.1)] using L.tooth p (sw hp.1 hp)
  · intro p hp; have orig := L.star p (sw hp.1 hp)
    dsimp only at orig ⊢; unfold starPos rootAt exitAt at orig ⊢; rw [eq _ (wide hp.1)] at orig; exact orig
  · intro p hp all; have test := L.patch p hp (fun b => by simpa only [onB,eq _ (wide_off hp b)] using all b)
    simpa only [patchPos,eq p (wide hp)] using test
  · intro p hp d inb; apply L.bonds p (sw hp.1 hp); simpa only [onB,eq _ (wide_shift hp.1 d)] using inb
  · intro p hp; exact L.turns p (sw hp.1 hp)
  · intro p hp; exact L.extSites p (sw hp.1 hp)
  · intro p hp; simpa only [cellB,eq p (wide hp)] using L.faces p hp
  · intro p hp; simpa only [cellB,eq p (wide hp)] using L.faceOff p hp
  · intro p hp d; simpa only [onB,eq _ (wide_shift hp.1 d)] using L.extOff p (sw hp.1 hp) d
  · intro p hp v inb; apply L.freeEdges p (sw hp.1 hp); simpa only [onB,eq _ (wide_base hp.1 v)] using inb

private theorem axis_data {k g a i δ : Int} (ha : 0≤a) (lo : 8≤g) (hi : g+9≤k) (off : -6≤δ ∧ δ≤11) :
    let x := site i δ; let y := site (fold g a i) δ
    (0≤x ↔ 0≤y) ∧ (x<3*(k+a)+2 ↔ y<3*k+2) ∧ (x<3*(k+a)+1 ↔ y<3*k+1) ∧
    clip x=clip y ∧ clip (3*(k+a)+1-x)=clip (3*k+1-y) ∧
    rep 23 (k+a-7) x=rep 23 (k-7) y ∧ rep 21 (k+a-7) x=rep 21 (k-7) y := by
  unfold site fold; split_ifs <;> dsimp only <;> refine ⟨by omega,by omega,by omega,?_,?_,?_,?_⟩
  all_goals first | unfold rep; split_ifs <;> omega | unfold clip; omega

private def axisData (k i δ : Int) :=
  let x := site i δ
  (decide (0≤x),decide (x<3*k+2),decide (x<3*k+1),clip x,clip (3*k+1-x),rep 23 (k-7) x,rep 21 (k-7) x)
private theorem axis_fold {k g a i δ : Int} (ha : 0≤a) (lo : 8≤g) (hi : g+9≤k) (off : -6≤δ ∧ δ≤11) :
    axisData (k+a) i δ=axisData k (fold g a i) δ := by
  obtain ⟨A,B,C,D,E,F,G⟩ := axis_data (i:=i) ha lo hi off
  simp only [axisData,Prod.mk.injEq]; exact ⟨decide_eq_decide.mpr A,decide_eq_decide.mpr B,decide_eq_decide.mpr C,D,E,F,G⟩

theorem sig_fold {a b q i j : Int} (ha : 0≤a) (hb : 0≤b) (L : 0<a → 12≤q) (R : 0<b → q≤12)
    (p : Pos) (hp : fringe p) :
    sig (25+a+b) (q+a) i j p=sig 25 q (shortCol a b i) (row a b j) p := by
  have x1 := axis_fold (k:=25+b) (g:=8) (i:=i) ha (by decide) (by omega) hp.2.2
  have x2 := axis_fold (k:=25) (g:=16) (i:=fold 8 a i) hb (by decide) (by decide) hp.2.2
  have y := axis_fold (k:=25) (g:=8) (i:=j) (show 0≤a+b by omega) (by decide) (by decide) ⟨hp.1,hp.2.1⟩
  rw [show 25+b+a=25+a+b by ring] at x1; rw [show 25+(a+b)=25+a+b by ring] at y
  have x := x1.trans x2
  simp only [axisData,Prod.mk.injEq,decide_eq_decide] at x y
  have ex : (site i p.2-(2+3*(q+a))<0 ↔ site (shortCol a b i) p.2-(2+3*q)<0) ∧
      (site i p.2=2+3*(q+a) ↔ site (shortCol a b i) p.2=2+3*q) := by
    unfold site shortCol fold; unfold fringe at hp; split_ifs <;> omega
  have ze (z : Int) : clip z=0 ↔ z=0 := by unfold clip; omega
  have neg (z : Int) : clip z<0 ↔ z<0 := by unfold clip; omega
  have y0 : site j p.1=0 ↔ site (row a b j) p.1=0 := by rw [←ze,←ze (site (row a b j) p.1)]; exact y.2.2.2.1 ▸ Iff.rfl
  have x0 : site i p.2=0 ↔ site (shortCol a b i) p.2=0 := by rw [←ze,←ze (site (shortCol a b i) p.2)]; exact x.2.2.2.1 ▸ Iff.rfl
  have eqZ : clip (site i p.2-(2+3*(q+a)))=0 ↔ clip (site (shortCol a b i) p.2-(2+3*q))=0 := by
    rw [ze,ze,sub_eq_zero,sub_eq_zero]; exact ex.2
  have eqN := (neg _).trans (ex.1.trans (neg _).symm)
  have rx : site (fold 16 b (fold 8 a i)) p.2=site (shortCol a b i) p.2 := rfl
  have ry : site (fold 8 (a+b) j) p.1=site (row a b j) p.1 := rfl
  simp only [rx] at x; simp only [ry] at y
  unfold sig shiftAt; dsimp only; unfold rimDatum inside representative
  simp only [show 3*(25+a+b)+2-1=3*(25+a+b)+1 by ring,show 3*(25:Int)+2-1=3*25+1 by ring,
    x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2.1,x.2.2.2.2.2.2,
    y.1,y.2.1,y.2.2.1,y.2.2.2.1,y.2.2.2.2.1,y.2.2.2.2.2.1,y.2.2.2.2.2.2,
    not_congr eqZ,eqZ,eqN,y0,x0,ex.2]

/-- The projection has a single global source for its marks, directions,
turn bits and matching bits. Every occurrence satisfies the *base*
local constraints, including occurrences wholly inside an insertion. -/
theorem physical_to_folded {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (canon : packed (signature (by omega) F)=code4 0 0 1 1) :
    ∃ P q s, North.Chart F P (2+3*q) ∧ Global F P s ∧
      (∀ i j : Int, four (pull s i j)=actual F i j) ∧
      ((u=0 ∧ 1≤q ∧ q≤9 ∧ ∀ i j : Int, Local (sig 11 q i j) (pull s i j)) ∨
       ∃ p a b : Nat, 1≤p ∧ p≤23 ∧ q=p+a ∧ 11+14*u=25+a+b ∧
        (0<a → 12≤p) ∧ (0<b → p≤12) ∧ ∀ i j : Int,
        Local (sig 25 p (shortCol a b i) (row a b j)) (pull s i j)) := by
  obtain ⟨P,q,C,cover,_⟩ := North.short_fold_chart F acy score two canon
  obtain ⟨s,g⟩ := global_of_score C acy score
  refine ⟨P,q,s,C,g,?_,?_⟩
  · intro i j; unfold actual four; funext t
    simp only [pull,maskField,Function.comp_apply,g.marks]
  · have L := physical_box F acy score canon C g
    rcases cover with ⟨rfl,lo,hi⟩|⟨p,a,b,lo,hi,ex,sz,left,right⟩
    · exact Or.inl ⟨rfl,lo,hi,by simpa using L⟩
    · refine Or.inr ⟨p,a,b,lo,hi,ex,sz,left,right,?_⟩
      intro i j
      have W := L i j
      rw [ex,show 11+14*(u:Int)=25+a+b by exact_mod_cast sz,Nat.cast_add] at W
      exact local_congr (sig_fold (Int.natCast_nonneg a) (Int.natCast_nonneg b)
        (by exact_mod_cast left) (by exact_mod_cast right)) W

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
