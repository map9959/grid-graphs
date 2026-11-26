import Mathlib

namespace GridGraphs.NoPitch.Dual
open Finset

/-- Twice the RHS: ordinary integer coefficients in the six-side step `t`. -/
structure Poly where
  a : Int
  b : Int
  c : Int
deriving Inhabited, DecidableEq, Repr

def Poly.atStep (p : Poly) (t : Int) := p.a+p.b*t+p.c*t^2
structure Row where
  source : Nat
  sense : Nat -- 0 equality, 1 ≤, 2 ≥
  y : Int -- signed multiplier after clearing all denominators
  rhs : Poly
deriving Inhabited

structure Col where
  key : Nat
  units : Nat
  fixed : Bool
  objective : Int
  terms : List (Nat × Int)
deriving Inhabited

structure Chart where
  scale : Nat
  rows : Array Row
  cols : Array Col
deriving Inhabited

def w (R : Array Row) (i : Nat) := if h : i<R.size then R[i].y else 0
def coeff (i : Nat) (a : List (Nat × Int)) :=
  (a.map (fun p => if p.1=i then p.2 else 0)).sum
def dot (R : Array Row) (a : List (Nat × Int)) :=
  (a.map (fun p => w R p.1*p.2)).sum

private theorem exchange (R : Array Row) (a : List (Nat × Int)) :
    dot R a = ∑ i : Fin R.size, R[i].y*coeff i a := by
  induction a with
  | nil => simp [dot,coeff]
  | cons p a ih =>
    rcases p with ⟨j,v⟩
    simp only [dot,List.map_cons,List.sum_cons,coeff,mul_add,sum_add_distrib] at ih ⊢
    rw [ih]; congr 1
    by_cases h : j<R.size
    · let q : Fin R.size := ⟨j,h⟩
      calc
        w R j*v = ∑ i : Fin R.size, if i=q then R[i].y*v else 0 := by simp [q,w,h]
        _ = _ := by
          apply sum_congr rfl; intro i _
          by_cases eq : i=q
          · subst i; simp [q]
          · have ne : j≠i.val := fun e => eq (Fin.ext e.symm)
            simp [ne,eq]
    · have ne (i : Fin R.size) : j≠i.val := by have := i.isLt; omega
      simp [w,h,ne]

def price (D : Chart) (i : Fin D.cols.size) :=
  if D.cols[i].fixed then 0 else max 0 ((D.scale:Int)*D.cols[i].objective-dot D.rows D.cols[i].terms)
def repair (D : Chart) := ∑ i : Fin D.cols.size, price D i
def rhsSum (D : Chart) : Poly :=
  ⟨∑ i : Fin D.rows.size, D.rows[i].y*D.rows[i].rhs.a,
   ∑ i : Fin D.rows.size, D.rows[i].y*D.rows[i].rhs.b,
   ∑ i : Fin D.rows.size, D.rows[i].y*D.rows[i].rhs.c⟩

def score (D : Chart) (x : Fin D.cols.size → Int) :=
  ∑ j : Fin D.cols.size, D.cols[j].objective*x j
def lhs (D : Chart) (x : Fin D.cols.size → Int) (i : Fin D.rows.size) :=
  ∑ j : Fin D.cols.size, coeff i D.cols[j].terms*x j
def rowHolds (s : Nat) (l r : Int) : Prop :=
  if s=0 then l=r else if s=1 then l≤r else l≥r
def signOK (r : Row) := r.sense==0 || (r.sense==1 && r.y≥0) || (r.sense==2 && r.y≤0)

/-- Physical orbit counts are eightfold integers. Only the positive
residual columns need an upper bound; on the tails there are none. -/
structure Feasible (D : Chart) (x : Fin D.cols.size → Int) (mass t cap : Int) : Prop where
  nonneg : ∀ j, 0 ≤ x j
  forbidden : ∀ j, D.cols[j].fixed=true → x j=0
  bounded : ∀ j, 0 < price D j → x j ≤ cap
  rows : ∀ i, rowHolds D.rows[i].sense (2*lhs D x i) (mass*D.rows[i].rhs.atStep t)

theorem replay_bound (D : Chart) {x mass t cap} (physical : Feasible D x mass t cap)
    (signs : D.rows.all signOK) :
    2*(D.scale:Int)*score D x ≤ mass*(rhsSum D).atStep t + 2*cap*repair D := by
  have cols (j : Fin D.cols.size) :
      (D.scale:Int)*D.cols[j].objective*x j ≤ dot D.rows D.cols[j].terms*x j + cap*price D j := by
    by_cases fix : D.cols[j].fixed
    · rw [physical.forbidden j fix,price,if_pos fix]; simp
    have p : price D j = max 0 ((D.scale:Int)*D.cols[j].objective-dot D.rows D.cols[j].terms) := by
      rw [price,if_neg fix]
    by_cases bad : dot D.rows D.cols[j].terms < (D.scale:Int)*D.cols[j].objective
    · have pos : 0<price D j := by rw [p]; omega
      have b := mul_le_mul_of_nonneg_right (physical.bounded j pos) pos.le
      rw [p,max_eq_right (by omega)] at b ⊢
      linarith
    · rw [p,max_eq_left (by omega)]
      simpa using mul_le_mul_of_nonneg_right (le_of_not_gt bad) (physical.nonneg j)
  have rowBound (i : Fin D.rows.size) :
      D.rows[i].y*(2*lhs D x i) ≤ D.rows[i].y*(mass*D.rows[i].rhs.atStep t) := by
    have good := Array.all_eq_true_iff_forall_mem.mp signs _ (Array.getElem_mem i.isLt)
    have row := physical.rows i
    simp [signOK] at good
    rcases good with (e|⟨e,s⟩)|⟨e,s⟩
    · simp [rowHolds,e] at row; rw [row]; rfl
    · simp [rowHolds,e] at row; exact mul_le_mul_of_nonneg_left row s
    · simp [rowHolds,e] at row; exact mul_le_mul_of_nonpos_left row s
  have matrix : (∑ j : Fin D.cols.size, dot D.rows D.cols[j].terms*x j) =
      ∑ i : Fin D.rows.size, D.rows[i].y * lhs D x i := by
    simp only [exchange,sum_mul,lhs,mul_sum,mul_assoc]; rw [sum_comm]
  have poly : (∑ i : Fin D.rows.size, D.rows[i].y*(mass*D.rows[i].rhs.atStep t)) =
      mass*(rhsSum D).atStep t := by
    simp only [rhsSum,Poly.atStep,sum_mul,mul_sum,←sum_add_distrib]
    apply sum_congr rfl; intro i _; ring
  have a := sum_le_sum (fun j (_ : j∈univ) => cols j)
  have b := sum_le_sum (fun i (_ : i∈univ) => rowBound i)
  rw [sum_add_distrib,matrix,←mul_sum] at a
  rw [poly] at b
  simp_rw [show ∀ i : Fin D.rows.size, D.rows[i].y*(2*lhs D x i)=2*(D.rows[i].y*lhs D x i)
    by intro; ring] at b
  rw [←mul_sum] at b
  unfold repair score
  simp only [mul_assoc,←mul_sum] at a
  linarith

end GridGraphs.NoPitch.Dual
