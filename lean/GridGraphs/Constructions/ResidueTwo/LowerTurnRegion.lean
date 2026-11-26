import GridGraphs.Constructions.ResidueTwo.LowerTurnExpr
import GridGraphs.Constructions.ResidueTwo.LowerTurnSplit
import GridGraphs.Constructions.ResidueTwo.LowerTurnLayers

namespace GridGraphs.ResidueTwoLower.Poly

structure Pitch where
  t : Nat
  i : Nat
  j : Nat

def subst (p : Pitch) (a b c : Nat) (di dj : ℤ) : Sub :=
  ⟨⟨p.t,0,0,a⟩,⟨0,p.i,0,(b:ℤ)+di⟩,⟨0,0,p.j,(c:ℤ)+dj⟩⟩

private theorem sub_eval (p : Pitch) (hp : 0<p.t ∧ 0<p.i ∧ 0<p.j) (t i j di dj : ℤ) :
    let s := subst p (t%p.t).toNat (i%p.i).toNat (j%p.j).toNat di dj
    s.t.val (t/p.t) (i/p.i) (j/p.j)=t ∧ s.i.val (t/p.t) (i/p.i) (j/p.j)=i+di ∧
    s.j.val (t/p.t) (i/p.i) (j/p.j)=j+dj := by
  have nonneg (x : ℤ) (n : Nat) (h : 0<n) : 0 ≤ x%(n:ℤ) := Int.emod_nonneg _ (by omega)
  simp [subst,Lin.val,Int.toNat_of_nonneg (nonneg t p.t hp.1),
    Int.toNat_of_nonneg (nonneg i p.i hp.2.1),Int.toNat_of_nonneg (nonneg j p.j hp.2.2),
    ←add_assoc,Int.mul_ediv_add_emod]

/-- A query is a conjunction of possibly shifted regions. `false` negates
the region. All offsets apply to actual sites, including at the boundary. -/
structure Lit where
  region : Region
  di : ℤ := 0
  dj : ℤ := 0
  pos : Bool := true

def Lit.Holds (a : Lit) (t i j : ℤ) :=
  if a.pos then a.region.eval t (i+a.di) (j+a.dj) else ¬ a.region.eval t (i+a.di) (j+a.dj)

def Lit.lower (p : Pitch) (a : Lit) (t i j : Nat) : Option Formula := do
  let f ← a.region.lower (subst p t i j a.di a.dj)
  return if a.pos then f else f.neg

def checkResidue (p : Pitch) (query : List Lit) (t i j : Nat) : Bool :=
  match query.mapM (fun a => a.lower p t i j) with
  | none => false
  | some fs => solve (fs.map Formula.weight).sum [] (fs.foldr Formula.band .yes)

def checkAt (p : Pitch) (query : List Lit) : Bool :=
  (List.range p.t).all fun t => (List.range p.i).all fun i =>
    (List.range p.j).all fun j => checkResidue p query t i j

private theorem checkAt_sound (p : Pitch) (hp : 0<p.t ∧ 0<p.i ∧ 0<p.j) {query : List Lit}
    (ok : checkAt p query = true) (t i j : ℤ) : ¬ ∀ a ∈ query, a.Holds t i j := by
  intro h
  simp [checkAt] at ok
  have bd (x : ℤ) (n : Nat) (hn : 0<n) : (x%n).toNat<n := by
    have lt := Int.emod_lt_of_pos x (show 0<(n:ℤ) by omega)
    omega
  specialize ok (t%p.t).toNat (bd _ _ hp.1) (i%p.i).toNat (bd _ _ hp.2.1)
    (j%p.j).toNat (bd _ _ hp.2.2)
  let A := (t%(p.t:ℤ)).toNat
  let B := (i%(p.i:ℤ)).toNat
  let C := (j%(p.j:ℤ)).toNat
  change checkResidue p query A B C=true at ok
  unfold checkResidue at ok
  split at ok
  · contradiction
  · rename_i fs hm
    have all {ls : List Lit} {xs : List Formula}
        (eq : ls.mapM (fun a => a.lower p A B C) = some xs)
        (hl : ∀ a∈ls, a.Holds t i j) : ∀ f∈xs, f.denote (t/p.t) (i/p.i) (j/p.j) := by
      induction ls generalizing xs with
      | nil => simp at eq; subst xs; simp
      | cons a ls ih =>
        have ha := hl a (by simp)
        cases ea : a.lower p A B C with
        | none => simp [List.mapM_cons,ea] at eq
        | some f =>
          cases es : ls.mapM (fun a => a.lower p A B C) with
          | none => simp [List.mapM_cons,ea,es] at eq
          | some ss =>
            simp [List.mapM_cons,ea,es] at eq
            subst xs
            apply List.forall_mem_cons.mpr ⟨?_,ih es (fun x hx => hl x (by simp [hx]))⟩
            unfold Lit.lower at ea
            cases ef : a.region.lower (subst p A B C a.di a.dj) with
            | none => simp [ef] at ea
            | some v =>
              have good := Region.lower_sound _ _ (t/p.t) (i/p.i) (j/p.j) ef
              obtain ⟨ht,hi,hj⟩ := sub_eval p hp t i j a.di a.dj
              change (subst p A B C a.di a.dj).t.val _ _ _ = _ at ht
              change (subst p A B C a.di a.dj).i.val _ _ _ = _ at hi
              change (subst p A B C a.di a.dj).j.val _ _ _ = _ at hj
              rw [ht,hi,hj] at good
              cases pos : a.pos <;> simp [pos,ef] at ea <;> subst f <;>
                simpa [Lit.Holds,pos,good] using ha
    have yes (ls : List Formula) (all : ∀ x ∈ ls, x.denote (t/p.t) (i/p.i) (j/p.j)) :
        (ls.foldr Formula.band .yes).denote (t/p.t) (i/p.i) (j/p.j) := by
      induction ls with
      | nil => trivial
      | cons a ls ih =>
        simp only [List.foldr_cons,Formula.band_denote]
        exact ⟨all a (by simp),ih (fun x hx => all x (by simp [hx]))⟩
    have res := solve_sound (fs.map Formula.weight).sum (t := t/p.t) (i := i/p.i) (j := j/p.j)
      (cs := []) (by simp [Holds]) (yes _ (all hm h))
    rw [res] at ok
    contradiction

/-- Select the least pitch which can linearize the query. Compatibility
depends only on the coefficients, irrespective of the residue constants.
The soundness proof nevertheless checks every residue at the selected pitch. -/
def candidates : List Pitch :=
  [⟨1,1,1⟩,⟨1,1,3⟩,⟨1,7,3⟩,⟨1,7,6⟩,⟨1,14,3⟩,⟨2,14,3⟩,⟨2,14,6⟩]

def check (query : List Lit) : Bool :=
  match candidates.find? (fun p => query.all fun a => (a.lower p 0 0 0).isSome) with
  | none => false
  | some p => (0<p.t && 0<p.i && 0<p.j) && checkAt p query

theorem check_sound {query : List Lit} (ok : check query = true) (t i j : ℤ) :
    ¬ ∀ a ∈ query, a.Holds t i j := by
  unfold check at ok
  split at ok
  · contradiction
  · simp only [Bool.and_eq_true,decide_eq_true_eq] at ok
    exact checkAt_sound _ ⟨ok.1.1.1,ok.1.1.2,ok.1.2⟩ ok.2 t i j

end GridGraphs.ResidueTwoLower.Poly
