import GridGraphs.ResidueTwoUpper.TwoGapCrop
import GridGraphs.Geometry.FoldedStripCover

/-! Exact local coordinate transport for the two-gap 623 chart. A plaquette
has origin `1+3*i`, six sites and a four-site halo: offsets `-4..9`.
`axis` is the same integer stencil index as the physical upper proof uses.
The transport includes reflected indices, not just near-wall distances. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap
open ResidueZero FoldedStripCover

def fold (g a i : Int) := if i≤g then i else max g (i-a)
def site (i δ : Int) := 1+3*i+δ
def chart (k i δ : Int) :=
  let n := 3*k+2
  let x := site i δ
  (decide (0≤x ∧ x<n),axis n 6 x,axis n 6 (n-1-x),
    axis (n-2) 5 x,axis (n-2) 5 (n-3-x))

theorem chart_fold {k g a i δ : Int} (lo : 8≤g) (hi : g+9≤k)
    (ha : 0≤a) (off : -4≤δ ∧ δ≤9) :
    chart (k+a) i δ=chart k (fold g a i) δ := by
  have eqAxis (i : Int) (d t h : Int) (hd : 5≤d ∧ d≤6) (ht : 0≤t ∧ t≤2)
      (hh : -6≤h ∧ h≤11) :
      axis (3*(k+a)+2-t) d (3*i+h)=axis (3*k+2-t) d (3*fold g a i+h) ∧
      axis (3*(k+a)+2-t) d (3*(k+a-i)-h)=axis (3*k+2-t) d (3*(k-fold g a i)-h) := by
    unfold fold; split_ifs <;> rcases le_total g (i-a) with m|m <;>
      (try simp only [max_eq_right m,max_eq_left m]) <;> constructor <;> unfold axis <;> split_ifs <;> omega
  have star := eqAxis i 6 0 (1+δ) (by decide) (by decide) (by omega)
  have refl := eqAxis i 6 0 δ (by decide) (by decide) (by omega)
  have patch := eqAxis i 5 2 (1+δ) (by decide) (by decide) (by omega)
  have reflP := eqAxis i 5 2 (2+δ) (by decide) (by decide) (by omega)
  unfold chart site
  apply Prod.ext
  · dsimp; apply Bool.eq_iff_iff.mpr; simp; unfold fold; split_ifs <;> omega
  · simp only [Prod.mk.injEq]; ring_nf at *; exact ⟨star.1,refl.2,patch.1,reflP.2⟩

/-- All comparisons in the canonical rim word, parent and depth-two
tooth guards factor through these three clipped signed distances. -/
def clip (x : Int) := max (-4) (min 4 x)
def nearEnds (k i δ : Int) := (clip (site i δ), clip (3*k+1-site i δ))
def deep (k i : Int) := decide (4 ≤ i ∧ i+5≤k)

theorem ends_fold {k g a i δ : Int} (lo : 8≤g) (hi : g+9≤k)
    (ha : 0≤a) (off : -4≤δ ∧ δ≤9) :
    nearEnds (k+a) i δ=nearEnds k (fold g a i) δ ∧
    ∀ b : Int, 0≤b → b≤1 → deep (k+a) (i+b)=deep k (fold g a i+b) := by
  unfold nearEnds site clip fold deep; split_ifs <;> constructor
  all_goals first
    | apply Prod.ext <;> dsimp <;> omega
    | intro b lo hi; apply Bool.eq_iff_iff.mpr; simp; omega

/-- In the 623 chart the entire horizontal exit guard translates, not
only the phase of the charged star. The offset is preserved exactly
whenever the exit is inside the fourteen-site box. -/
def col (a b x : Int) := fold 198 b (fold 8 a x)
def row (a b y : Int) := fold 8 (a+b) y
def exitΔ (q i δ : Int) := site i δ-(2+3*q)
theorem exit_fold {a b q i δ : Int} (ha : 0≤a) (hb : 0≤b)
    (hq : 102≤q ∧ q≤104) (off : -4≤δ ∧ δ≤9) :
    clip (exitΔ (q+a) i δ)=clip (exitΔ q (col a b i) δ) := by
  unfold clip exitΔ site col fold
  split_ifs <;> omega

def tileKey (k q i j δ ε : Int) :=
  (chart k i δ, chart k j ε, nearEnds k i δ, nearEnds k j ε,
    clip (exitΔ q i δ), deep k i,deep k (i+1),deep k j,deep k (j+1))

theorem key_fold {a b q i j δ ε : Int} (ha : 0≤a) (hb : 0≤b)
    (hq : 102≤q ∧ q≤104) (dx : -4≤δ ∧ δ≤9) (dy : -4≤ε ∧ ε≤9) :
    tileKey (207+a+b) (q+a) i j δ ε=tileKey 207 q (col a b i) (row a b j) δ ε := by
  have fold1 := chart_fold (k:=207+b) (g:=8) (i:=i) (by decide) (by omega) ha dx
  have fold2 := chart_fold (k:=207) (g:=198) (i:=fold 8 a i) (by decide) (by decide) hb dx
  have fold3 := chart_fold (k:=207) (g:=8) (i:=j) (by decide) (by decide) (show 0≤a+b by omega) dy
  have a1 := ends_fold (k:=207+b) (g:=8) (i:=i) (by decide) (by omega) ha dx
  have a2 := ends_fold (k:=207) (g:=198) (i:=fold 8 a i) (by decide) (by decide) hb dx
  have a3 := ends_fold (k:=207) (g:=8) (i:=j) (by decide) (by decide) (show 0≤a+b by omega) dy
  unfold tileKey col row
  have e1 : 207+a+b=207+b+a := by omega
  have e2 : 207+a+b=207+(a+b) := by omega
  rw [←e1] at fold1 a1; rw [←e2] at fold3 a3
  have end0 {k z l w : Int} (h : ∀ v : Int, 0≤v → v≤1 → deep k (z+v)=deep l (w+v)) :
      deep k z=deep l w := by simpa using h 0 (by decide) (by decide)
  simp only [fold1,fold2,fold3,a1.1,a2.1,a3.1,exit_fold ha hb hq dx,col,
    end0 a1.2,end0 a2.2,end0 a3.2,a1.2 1 (by decide) (by decide),
    a2.2 1 (by decide) (by decide),a3.2 1 (by decide) (by decide)]

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap
