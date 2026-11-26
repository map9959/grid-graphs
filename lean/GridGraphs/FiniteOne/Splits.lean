import GridGraphs.FiniteOne.Sound

namespace GridGraphs.FiniteOne
open ResidueZero Finset

/-- No symmetry of the forest is assumed: this is an integer count on
the union of physical images, counting each *site* just once. -/
def orbit (n : Nat) (x : Pos) (p : Pos) := (List.range 8).any fun g => image n g x == p
def occ {n} (F : Finset (GridVertex n n)) (x : Pos) : Int :=
  ∑ v : GridVertex n n, (if orbit n x (coord v) then (1:Int) else 0)*(decide (v∈F)).toNat

structure Cut where
  x : Pos
  weight : Int
  limit : Int
def Cut.holds {n} (F : Finset (GridVertex n n)) (c : Cut) :=
  c.weight*occ F c.x ≤ c.weight*c.limit
def charges (n : Nat) (cs : List Cut) (p : Pos) : Int :=
  (cs.map (fun c => if orbit n c.x p then c.weight else 0)).sum
def allowance (cs : List Cut) := (cs.map (fun c => c.weight*c.limit)).sum

theorem charges_le {n} (F : Finset (GridVertex n n)) (cs : List Cut)
    (ok : ∀ c∈cs, c.holds F) :
    (∑ v : GridVertex n n, charges n cs (coord v)*(decide (v∈F)).toNat) ≤ allowance cs := by
  induction cs with
  | nil => simp [charges,allowance]
  | cons c cs ih =>
    have b := ok c (by simp); have t := ih (fun a m => ok a (by simp [m]))
    have e (v : GridVertex n n) : (if orbit n c.x (coord v) then c.weight else 0) =
        c.weight*(if orbit n c.x (coord v) then (1:Int) else 0) := by split <;> simp
    simpa only [charges,allowance,List.map_cons,List.sum_cons,add_mul,sum_add_distrib,e,
      mul_assoc,←mul_sum,occ] using (show c.weight*occ F c.x+
      (∑ v : GridVertex n n, charges n cs (coord v)*(decide (v∈F)).toNat) ≤ c.weight*c.limit+allowance cs from add_le_add b t)

theorem cut_bound {n b} (hn : 2≤n) (T : Prices) (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic)
    (cs : List Cut) (ok : ∀ c∈cs, c.holds F)
    (test : pricedBudget T n (charges n cs)+allowance cs<(T.unit:Int)*(b+1:Nat)) : F.card≤b := by
  have a := charged_sound hn T F acy (charges n cs)
  have h := charges_le F cs ok
  by_contra! bad
  have s : ((b+1:Nat):Int) ≤ F.card := by omega
  have z := mul_le_mul_of_nonneg_left s (Int.natCast_nonneg T.unit)
  linarith only [a,h,test,z]
end GridGraphs.FiniteOne
