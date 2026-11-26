import GridGraphs.NoPitch.TailRows.BucketCounts

namespace GridGraphs.NoPitch.TailRows
open Keys GridGraphs.NoPitch.Dual
structure NormShape where
  n : Nat
  collar : Nat
  pattern : List Nat
  strip : Strip
  polynomial : Poly
  deriving Inhabited

def NormShape.Valid (v : NormShape) := ∀ u : Nat,
  0 ≤ v.strip.height u ∧ v.strip.bounds (v.n+6*u) u ∧
    v.strip.fibre (v.n+6*u) v.collar u v.pattern ∧ v.strip.size2 u=v.polynomial.atStep u

theorem NormShape.count (v : NormShape) (valid : v.Valid) (u : Nat) :
    2*((Finset.univ.filter (fun p : Fin (v.n+6*u) × Fin (v.n+6*u) =>
      fine (v.n+6*u) v.collar p.1.val p.2.val=v.pattern)).card:Int)=v.polynomial.atStep u := by
  obtain ⟨a,b,c,d⟩ := valid u; rw [←d]; exact count_strip _ _ _ _ _ a b c

theorem axis_crit (n h x a : Nat) (hx : x<n) (hn : 2*h+3≤n) :
    axis n h x=a ↔ if a<h then x=a else if a<h+3 then h≤x ∧ x<n-h ∧ (x-h)%3=a-h
      else n-h≤x ∧ 2*h+3+x=n+a := by
  unfold axis; split_ifs <;> omega

theorem clip_crit (x : Int) (a : Nat) :
    clip x=a ↔ if a=0 then x≤ -9 else if a=18 then 9≤x else a≤18 ∧ x=(a:Int)-9 := by
  unfold clip; simp only [max_def,min_def]; split_ifs <;> omega

macro "verify_strip" : tactic => `(tactic|
  (intro u
   refine ⟨?_,?_,?_,?_⟩
   · dsimp [Strip.height]; omega
   · intro i hi
     dsimp [Strip.height] at hi
     dsimp [Strip.X,Strip.Y,Strip.width]
     push_cast
     refine ⟨?_,?_,?_,?_⟩ <;> first | omega | (intro j hj; constructor <;> omega)
   · intro x y hx hy
     simp only [fine,List.cons.injEq,and_true]
     dsimp only [Strip.X,Strip.Y,Strip.height,Strip.width]
     simp (disch := omega) only [axis_crit _ _ x _ hx,axis_crit _ _ y _ hy,clip_crit]
     norm_num <;> omega
   · dsimp [Strip.size2,Strip.height,Poly.atStep]; ring))

end GridGraphs.NoPitch.TailRows
