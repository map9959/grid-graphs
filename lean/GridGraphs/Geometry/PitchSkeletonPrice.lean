import Mathlib

namespace GridGraphs.PitchSkeletonPrice

/-- Price of the coarse paths after charging their missing slots and double hits. -/
theorem joint (M base F E l v R C hits doubles r c : ℤ)
    (count : M = base+F-E-l-v)
    (missing : R-E+C ≤ l+hits) (atVacancy : hits ≤ v+doubles)
    (betweenRuns : doubles ≤ R-r-c) : M ≤ base+F-r-c-C := by omega

theorem skeleton (k s : ℤ) (price : s ≤ 3*(k+1)^2-(k+1)-2) :
    s ≤ 3*k^2+5*k := by nlinarith

/-- Round the mixed-window requirement before summing over gaps. -/
theorem interiorGap (i j e : ℤ) (bill : 3*e ≥ 3*(j-i)-1-4) :
    e ≥ j-i-1 := by omega

theorem firstStratum (F b C slack : ℤ)
    (coarse : 3647 = 3*35^2+F-35-b-C-slack) (forest : C ≥ 1)
    (account : 0 ≤ slack) (noPitch : 35-b ≤ F) :
    22 ≤ F ∧ (F = 22 → (b=13 ∨ b=14) ∧ C+slack ≤ 2) := by omega

/-- Remove the mandatory zero-hit vacancies on lines of the other axis.
The remaining correction is the *physical* join rank plus residual deficits. -/
theorem physicalPrice (m M F r c C j A s₁ s₂ s₃ : ℤ)
    (ledger : M = 3*m^2+F-r-c-C-s₁-s₂-s₃)
    (joins : C = A+j) (vac : 2*m-r-c ≤ s₂) (h₁ : 0 ≤ s₁) (h₃ : 0 ≤ s₃) :
    M ≤ (3*m-2)*m+F-j-A := by nlinarith

theorem effectiveFloor (F j A : ℤ) (p : 3647 ≤ 103*35+F-j-A)
    (root : 1 ≤ A) (rank : 0 ≤ j) :
    43 ≤ F-j ∧ (F=43 → A=1 ∧ j=0) := by omega

/-- Orient the nonisolated empty-stub junctions along a realized edge;
the isolated ones each consume a separate full-forest junction class. -/
theorem emptyStubFloor (F j A X iso waste : ℤ)
    (count : 3647 = 103*35+F-j-A-X)
    (classes : 1+iso ≤ A) (slack : waste ≤ X) :
    43+iso+waste ≤ F-j := by omega

/-- Combining two single-axis repairs pays only the rank shared by the
two seam systems, with duplicate deleted marks counted once. -/
theorem crossingExcludes (score row col overlap shared refill : ℤ)
    (cut : score-row-col+overlap-shared+refill ≤ 3568)
    (net : row+col-overlap+shared-refill ≤ 78) : score ≤ 3646 := by omega

/-- Each minority-axis coarse incidence requires a distinct blank join.
Use the physical run ledger, including isolates and weighted rim vacancies. -/
theorem coarseTurnBudget (n M T joins iso roots holes : ℤ)
    (ledger : joins+iso+2*roots+holes = n^2+4*n-3*M)
    (charge : T ≤ joins) (rh : 5 ≤ holes) (forest : 1 ≤ roots) (h : 0 ≤ iso) :
    T ≤ n^2+4*n-3*M-7 := by omega

theorem aboveCombTurns (k M T : ℤ)
    (score : 3*k^2+5*k+(3*k-13)/10+1 ≤ M)
    (bound : T ≤ (3*k+1)^2+4*(3*k+1)-3*M-7) :
    T ≤ 3*k-5-3*((3*k-13)/10) := by nlinarith

/-- Three physical bonds read from the face agree with an endpoint's
departure onto the coarse path. `chain` is the floor-tree parent rule;
the two middle vertices have at most one outgoing bond apiece. -/
theorem cornerPath {a b c p q r u v w : Prop}
    (ha : a ↔ p ∨ u) (hb : b ↔ q ∨ v) (hc : c ↔ r ∨ w)
    (chain : (p → q ∧ r) ∧ (w → v ∧ u))
    (mid : ¬(u ∧ q) ∧ ¬(v ∧ r)) :
    (a ∧ b ∧ c) ↔ (p ∨ w) := by tauto

/-- Last step of the integer-scaled dual check, after summing its
signed face/junction terms. It does not assume a segment placement. -/
theorem facePriceExclusion {ι : Type*} [Fintype ι]
    (weight face junction : ι → ℤ) (M : ℤ)
    (physical : ∀ i, face i = junction i)
    (dual : 10^12*M ≤ 3646644258657743 +
      ∑ i, weight i*(face i-junction i)) :
    M ≤ 3646 := by
  simp [physical] at dual
  omega

/-- The three physical rank branches at the second off-skeleton floor. -/
theorem secondFloorCases (C j A X : ℤ) (ledger : 3647 = 103*35+44-C-X)
    (full : A ≥ 1) (rank : j ≥ 0) (classes : C=A+j) (slack : X ≥ 0) :
    (C=1 ∧ j=0 ∧ X=1) ∨ (C=2 ∧ j=0 ∧ X=0) ∨ (C=2 ∧ j=1 ∧ X=0) := by omega

/-- At 45 off-skeleton marks choose a row of the six-case certificate
table: there are C choices for the actual join rank, not C+1. -/
theorem thirdFloorCases (C j A X : ℤ) (ledger : 3647 = 103*35+45-C-X)
    (full : A ≥ 1) (rank : j ≥ 0) (classes : C=A+j) (slack : X ≥ 0) :
    (C=1 ∧ X=2 ∧ j=0) ∨ (C=2 ∧ X=1 ∧ (j=0 ∨ j=1)) ∨
    (C=3 ∧ X=0 ∧ (j=0 ∨ j=1 ∨ j=2)) := by omega

/-- At any off-skeleton count on side 103 the branch indices fill a
triangle. At F=46 the four possible component counts give 10 cases. -/
theorem side103BranchRange (F C j A X : ℤ) (ledger : 3647 = 103*35+F-C-X)
    (full : A ≥ 1) (rank : j ≥ 0) (classes : C=A+j) (slack : X ≥ 0) :
    1 ≤ C ∧ C ≤ F-42 ∧ 0 ≤ j ∧ j < C ∧ X = F-42-C := by omega

/-- The two nontrivial zero-slack translations. In the interior,
`a` increments C alone and `b` increments C and j together. On the
outer edge only simultaneous increments are needed. -/
theorem zeroSlackTranslatedPrice (M a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (board : a+b ≤ 103^2-46)
    (price : 10^12*M ≤ 3641266687551126 - 699998257685*a + 460335*b ∨
             10^12*M ≤ 3641933434311821 + 107044*b) : M ≤ 3646 := by omega

/-- One exceptional line remains available throughout the `X=1` translation. -/
theorem oneSlackTranslatedPrice (M a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (board : a+b ≤ 103^2-47)
    (price : 10^12*M ≤ 3644535715973101 - 392857317626*a + 18036*b ∨
             10^12*M ≤ 3644857148726391 + 162407*b) : M ≤ 3646 := by omega

/-- Vertex check for a transported dual with two independent increments.
In the interior sector take a=C-j-3, b=j-2 and L=1225-5. -/
theorem trianglePrice (u p q a b L T : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (size : a+b ≤ L) (v₀ : u < T) (v₁ : u+p*L < T)
    (v₂ : u+q*L < T) : u+p*a+q*b < T := by
  rcases le_total p q with hp | hq
  · by_cases h : 0 ≤ q
    · nlinarith [mul_nonneg (sub_nonneg.mpr hp) ha, mul_nonneg h (sub_nonneg.mpr size)]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_trans hp (by omega)) ha,
                 mul_nonpos_of_nonpos_of_nonneg (show q ≤ 0 by omega) hb]
  · by_cases h : 0 ≤ p
    · nlinarith [mul_nonneg (sub_nonneg.mpr hq) hb, mul_nonneg h (sub_nonneg.mpr size)]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_trans hq (by omega)) hb,
                 mul_nonpos_of_nonpos_of_nonneg (show p ≤ 0 by omega) ha]

/-- Final integer implication of the free-count side-103 dual. The
external certificate supplies the scaled bound under the candidate
hypotheses; no component or slack parameter is fixed here. -/
theorem freeFaceGain (M F C X : ℤ) (ledger : M = 3605+F-C-X)
    (price : 10^12*M ≤ 3645265629022938) :
    F-C-X ≤ 40 ∧ M < 3647 := by omega

/-- Opposite pitch directions create separate junction classes at every
crossing. The integer-replayed prices cannot pay for six such classes. -/
theorem parallelPitch (p q A : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (lines : -10^12*(p+q) ≤ -6937498337446)
    (classes : 10^12*A ≤ 5813335418676) (crossings : p*q ≤ A) :
    7 ≤ p+q ∧ (p=0 ∨ q=0) := by
  have hn : 7 ≤ p+q := by omega
  refine ⟨hn, ?_⟩
  by_contra! bad
  have h₁ : 0 ≤ p-1 := by omega
  have h₂ : 0 ≤ q-1 := by omega
  have ha : A ≤ 5 := by omega
  nlinarith [mul_nonneg h₁ h₂]

/-- On an aligned pitch cut its incidence forest has one more component
than the total join deficit. All of these components contain junctions. -/
theorem alignedCapJoins (A ju jd : ℤ) (classes : A ≤ 5)
    (incidence : 1 ≤ 35-ju-jd ∧ 35-ju-jd ≤ A) :
    30 ≤ ju+jd ∧ ju+jd ≤ 34 := by omega

/-- Sufficient exterior cap tariffs at the outermost parallel cuts.
`band₀` and `band₁` are the two unwired band prices at weights 0 and 1. -/
theorem outerCaps103 (M u v p q : ℤ)
    (rp : 0 ≤ p ∧ p ≤ 34) (rq : 0 ≤ q ∧ q ≤ 34)
    (cu : (p=0 → u≤8) ∧ (0<p → p<34 → 10*u-7*p≤90) ∧ (p=34 → u≤33))
    (cv : (q=0 → v≤8) ∧ (0<q → q<34 → 10*v-7*q≤90) ∧ (q=34 → v≤33))
    (band₀ : M ≤ 3605+u+v) (band₁ : M ≤ 3605+u+v+34-p-q) :
    M ≤ 3646 := by omega

/-- Eliminate the run count from the ordinary edge and colored
neighborhood ledgers. `A` includes the pitch-row endpoints. -/
theorem slitBill (r j b R A U U₀ V X B : ℤ)
    (edges : 3*b = 3*r+j-U-X-R)
    (colors : 3*A-2*R-2*r = U-3*U₀+2*(R-r+j-X)-3*V)
    (bill : B=A-2*r+U+U₀+V+2*X) : 4*b=2*r+2*j-B := by omega

/-- Exact side-103 implication. The inputs are the old unrestricted
upper, the physical lower witness, the no-pitch exclusion and the
replayed cap certificate at the single forced pitch cut. -/
theorem side103Exact (P : ℤ) (comb : 3646 ≤ P) (oldUpper : P ≤ 3647)
    (atTarget : P=3647 → ∃ u v p q : ℤ,
      0≤p ∧ 0≤q ∧ p+q≤34 ∧ P=3605+u+v ∧
      (p<34 → 10*u-7*p≤89) ∧ (p=34 → u≤33) ∧
      (q<34 → 10*v-7*q≤89) ∧ (q=34 → v≤33)) : P=3646 := by
  by_contra no
  have eq : P=3647 := by omega
  obtain ⟨u,v,p,q,hp,hq,hj,hM,up,uc,vp,vc⟩ := atTarget eq
  omega

/-- Restating the pumped bill bound in physical marks. -/
theorem retainedTariff (k j b B : ℤ) (bill : 4*b = 2*(k+1)+2*j-B)
    (retained : 5*B ≥ 4*(k+1-j)+32) : 10*b-7*j ≤ 3*k-13 := by omega

/-- Combining the two physical cap tariffs on any width. The cut
rank inequality concerns both partitions in the same forest. -/
theorem uniformPitchBonus (k p q u v : ℤ) (hk : 5 ≤ k)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (shared : p+q ≤ k)
    (up : p<k → 10*u-7*p ≤ 3*k-13) (uc : p=k → u ≤ k-1)
    (vp : q<k → 10*v-7*q ≤ 3*k-13) (vc : q=k → v ≤ k-1) :
    u+v ≤ k-1+(3*k-13)/10 := by omega

/-- Integer rounding of the transported no-pitch dual after removing
the common quadratic baseline. -/
theorem uniformNoPitch (k excess : ℤ) (hk : 5 ≤ k)
    (price : 64*excess ≤ 336*k-79) : excess ≤ 5*k+(3*k-13)/10 := by omega

end GridGraphs.PitchSkeletonPrice
