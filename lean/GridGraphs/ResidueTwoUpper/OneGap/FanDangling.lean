import GridGraphs.ResidueTwoUpper.OneGap.FanRootTransport
import GridGraphs.Geometry.NorthFanLines

local macro "metric" : tactic => `(tactic| (try simp only [abs_eq_max_neg] at *; omega))

/-! Upper-side component of a dangling fan line, in the original forest.
The cut is between two consecutive physical rows, not between tile rows. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open ResidueZero L7

def coordinates {n : Nat} (w : View) (p : GridVertex n n) : Pos :=
  let x := reflect w.rowFar n (coord p).1; let y := reflect w.colFar n (coord p).2
  if w.swap then (y,x) else (x,y)
private theorem adjacent' {n} (w : View) {x y : GridVertex n n} (e : (gridGraph n n).Adj x y) :
    |(coordinates w x).1-(coordinates w y).1|+|(coordinates w x).2-(coordinates w y).2|=1 := by
  change adjacent _ _ _ _ at e; simp only [adjacent,Fin.ext_iff] at e
  cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [coordinates,coord,reflect] <;> metric
private theorem boundary' {n} (w : View) (p : GridVertex n n) (h : IsGridBoundary p) :
    (coordinates w p).1=0 ∨ (coordinates w p).2=0 ∨ (coordinates w p).1=n-1 ∨ (coordinates w p).2=n-1 := by
  unfold IsGridBoundary at h
  cases w with | mk a b s => cases a <;> cases b <;> cases s <;> simp [coordinates,coord,reflect] <;> omega

def nearLine (a d c rad : Int) (p : Pos) := ∃ z, a≤z ∧ z≤d ∧ |p.1-z|+|p.2-c|≤rad
def onLine (a d c : Int) (p : Pos) := p.2=c ∧ a≤p.1 ∧ p.1≤d
-- This records precisely the mark test that makes an upper path unrooted.
def clear {n} (F : Finset (GridVertex n n)) (w : View) (a d c : Int) :=
  ∀ v∈F, (coordinates w v).1≤d → nearLine a d c 2 (coordinates w v) → onLine a d c (coordinates w v)

theorem extend_clear {n} (F : Finset (GridVertex n n)) (w : View) (a d e c : Int) (ad : a≤d) (de : d≤e)
    (old : clear F w a d c)
    (slab : ∀ v∈F, d<(coordinates w v).1 → (coordinates w v).1≤e → |(coordinates w v).2-c|≤2 → (coordinates w v).2=c) :
    clear F w a e c := by
  intro v hv he hit; obtain ⟨z,az,ze,near⟩ := hit
  by_cases before : (coordinates w v).1≤d
  · have Q := old v hv before ⟨min z d,by metric,by metric,by metric⟩
    unfold onLine at *; metric
  · exact ⟨slab _ hv (by metric) he (by metric),by metric,he⟩

/-- The isolated-line lemma for the explicit fan is local: only the
marks in the two-site collar must agree with its word. Coordinates in
`NorthFanLines` omit the first physical row and column. -/
theorem fan_clear {n} (F : Finset (GridVertex n n)) (w : View) (q u d : Int) (hu : u≤q)
    (word : ∀ v∈F, (coordinates w v).1≤d → nearLine (q-u+3) d (3*u+1) 2 (coordinates w v) →
      ∃ i j a b, (coordinates w v)=(1+3*j+b,1+3*i+a) ∧ NorthFanLines.mark q i j a b) :
    clear F w (q-u+3) d (3*u+1) := by
  intro v hv he hit
  obtain ⟨i,j,a,b,eq,m⟩ := word v hv he hit
  obtain ⟨z,az,zd,near⟩ := hit
  rw [eq] at near ⊢; simp only [Prod.fst,Prod.snd] at near
  have I := NorthFanLines.isolated q u i j a b (z-1) hu (by metric) m (by metric)
  rw [eq] at he; dsimp [onLine] at *; metric

/-- Every vertex reached above the cut remains in the one-site collar;
there is no perimeter foot there. At most one edge crosses the cut, at
column c, even though non-line vertices in the window remain free. -/
theorem sealed {n} (F : Finset (GridVertex n n)) (w : View) (a d c : Int)
    (ha : 2≤a) (hd : d+2<n) (hc : 2≤c ∧ c+2<n) (empty : clear F w a d c)
    (next : ∀ v∈F, (coordinates w v).1=d+1 → |(coordinates w v).2-c|≤1 → (coordinates w v).2=c)
    (src : {p : GridVertex n n // (coordinates w p).1≤d}) (start : onLine a d c (coordinates w src.1))
    (v : {p : GridVertex n n // (coordinates w p).1≤d})
    (reach : ((Bonds F).induce {p | (coordinates w p).1≤d}).Reachable src v) :
    ¬IsGridBoundary v.1 ∧ ∀ y, (Bonds F).Adj v.1 y → d<(coordinates w y).1 →
      coordinates w v.1=(d,c) ∧ coordinates w y=(d+1,c) := by
  let G := (Bonds F).induce {p | (coordinates w p).1≤d}
  have first : nearLine a d c 1 (coordinates w src.1) := by
    obtain ⟨col,lo,hi⟩ := start; exact ⟨_,lo,hi,by rw [col]; simp⟩
  have stay {v x : {p : GridVertex n n // (coordinates w p).1≤d}} (h : nearLine a d c 1 (coordinates w v.1)) (e : G.Adj v x) : nearLine a d c 1 (coordinates w x.1) := by
    have E : (Bonds F).Adj v.1 x.1 := e
    have dist := adjacent' w E.1
    obtain ⟨z,az,zd,hh⟩ := h
    rcases E.2 with vm|xm
    · obtain ⟨col,lo,hi⟩ := empty _ vm v.2 ⟨z,az,zd,by metric⟩
      exact ⟨_,lo,hi,by metric⟩
    · obtain ⟨col,lo,hi⟩ := empty _ xm x.2 ⟨z,az,zd,by metric⟩
      exact ⟨_,lo,hi,by rw [col]; simp⟩
  obtain ⟨walk⟩ := reach
  have travel {s t : {p : GridVertex n n // (coordinates w p).1≤d}} (walk : G.Walk s t) :
      nearLine a d c 1 (coordinates w s.1) → nearLine a d c 1 (coordinates w t.1) := by
    induction walk with
    | nil => exact id
    | cons e _ ih => exact fun h => ih (stay h e)
  obtain ⟨z,az,zd,near⟩ := travel walk first
  constructor
  · intro bd; have := boundary' w _ bd; metric
  · intro y E beyond
    have dist := adjacent' w E.1; have := v.2
    have row : (coordinates w y).1=d+1 := by metric
    have same : (coordinates w v.1).2=(coordinates w y).2 := by metric
    have col : (coordinates w y).2=c := by
      rcases E.2 with vm|ym
      · exact same ▸ (empty _ vm v.2 ⟨z,az,zd,by metric⟩).1
      · exact next _ ym row (by metric)
    exact ⟨Prod.ext (by metric) (same.trans col),Prod.ext row col⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
