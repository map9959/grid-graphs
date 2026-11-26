import Mathlib

namespace GridGraphs.RadialComponentLedger

def score (i h g k c : ℤ) := 12*i + 4*h - 2*g - 3*k + 6*c
def cap (s : ℤ) := 4*s^2 + 14*s - 12

/-- Gluing the common rim consumes its entire number of classes. -/
theorem peel (s t i h hi g gi k ki c ci band : ℤ)
    (glue : c ≤ band+ci-gi)
    (localBound : 12*t+4*(h-hi)-2*g-4*gi-3*(k-ki)+6*band ≤ 48*s-60)
    (inner : score i hi gi ki ci ≤ cap (s-6)) :
    score (t+i) h g k c ≤ cap s := by
  have hcap : cap s-cap (s-6) = 48*s-60 := by unfold cap; ring
  unfold score at *
  omega

theorem projected (s i h g k c e : ℤ) (price : score i h g k c ≤ cap s)
    (joins : g-e+1 ≤ c) :
    12*i ≤ 4*s^2 + 14*s - 18 - 4*h - 4*g + 3*k + 6*e := by
  unfold score cap at price
  omega

theorem aboveComb (k h g corners c m : ℤ)
    (price : score m h g corners c ≤ cap (3*k+1))
    (better : 3*k^2+5*k+(3*k-13)/10+1 ≤ m) :
    4*h-2*g-3*corners+6*c ≤ 6*k-12*((3*k-13)/10)-6 := by
  unfold score cap at price
  nlinarith

theorem side103 (h g corners c m : ℤ) (price : score m h g corners c ≤ cap 103)
    (reaches : 3647 ≤ m) (gaps : g ≤ 7) (four : corners ≤ 4) (seen : 1 ≤ c) :
    h ≤ 30 := by
  unfold score cap at price
  norm_num at price
  omega

theorem canonical103 (h g : ℤ) (normalized : h ≤ 2*g+8) (gaps : g ≤ 7) :
    h ≤ 22 := by omega

theorem canonicalCorners103 (h g : ℤ) (normalized : h ≤ 2*g+4) (gaps : g ≤ 6) :
    h ≤ 16 := by omega

theorem samePitchRuns (r j u p e col : ℤ) (isols : 0 ≤ u)
    (components : p-1 ≤ j) (endCharge : e = 4*col + 2*p)
    (color : 6*(p-1)+2*j-e ≤ 4*r+u) :
    p-1 + (6*p-8-4*col+3)/4 ≤ r+j+u := by omega

theorem shiftedPitchRuns (r j u p e col : ℤ) (isols : 0 ≤ u)
    (components : p-1 ≤ j) (endCharge : e = 4*col+p)
    (color : 6*p+j-e ≤ 5*r+2*u) :
    p-1 + (6*p-1-4*col+4)/5 ≤ r+j+u := by omega

end GridGraphs.RadialComponentLedger
