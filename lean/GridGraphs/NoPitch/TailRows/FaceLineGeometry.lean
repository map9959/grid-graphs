import GridGraphs.NoPitch.TailRows.FaceLineChecks

namespace GridGraphs.NoPitch.TailRows.FaceLine
open PitchCut Keys FaceRows Budget LocalBoard19 GridGraphs.NoPitch.Dual Finset

private theorem rot_coord {k} [NeZero k] (g : Fin 8) (p : FacePos k) (a b : Fin 4) :
    let q := small 4 (invers g) (a,b)
    small (N k) g (coord p.1 q.1,coord p.2 q.2) =
      (coord (small k g p).1 a,coord (small k g p).2 b) := by
  have h := Incidence.pos g p
  have h' := Incidence.pos g (coord p.1 (small 4 (invers g) (a,b)).1,
    coord p.2 (small 4 (invers g) (a,b)).2)
  have w := Incidence.pos (invers g) (a,b)
  have := p.1.isLt; have := p.2.isLt; have := a.isLt; have := b.isLt
  dsimp only
  apply Prod.ext <;> apply Fin.ext
  all_goals
    fin_cases g <;> norm_num [invers,transform,N,Prod.ext_iff,coord] at h h' w ⊢ <;> omega

private theorem mask_bit {k} [NeZero k] (F : Finset (Site k)) (g : Fin 8) (p : FacePos k)
    (a b : Fin 4) :
    let q := small 4 (invers g) (a,b)
    faceMask F p q.1 q.2=faceMask (view F g) (small k g p) a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [faceMask,decide_eq_true_eq,←rot_coord]
  constructor
  · exact mem_image_of_mem _
  · intro h; obtain ⟨y,hy,e⟩ := mem_image.mp h
    exact (Function.LeftInverse.injective (Incidence.inverse g) e) ▸ hy

def stateAt {k} (F : Finset (Site k)) (g : Fin 8) (r : J k) (n : Nat) :=
  prefixState (view F g) (teeth k r) n

def sideRow {k} (r : Fin k) (a : Fin 2) : J k := ⟨r.val+a.val,by have := r.isLt; have := a.isLt; omega⟩

theorem word_eq {k} [NeZero k] (F : Finset (Site k)) (g : Fin 8) (p : FacePos k) (a : Fin 2) :
    let t := small k g p
    FaceLines.rotWord g (faceMask F p) a =
      FaceLines.stepWord (stateAt F g (sideRow t.1 a) (t.2.val+1))
        (stateAt F g (sideRow t.1 a) (t.2.val+2)) := by
  let t := small k g p
  calc
    _ = FaceLines.number (faceMask (view F g) t (cornerOffset a)) := by
      unfold FaceLines.rotWord
      simp only [List.range_succ,List.range_zero,List.foldl_append,List.foldl_cons,List.foldl_nil,mask_bit]
      change 0 + _ * 1 + _ * 2 + _ * 4 + _ * 8 = _ + 2*_ + 4*_ + 8*_
      ring_nf
      rfl
    _ = _ := by
      rw [edge_agrees]
      have eq : coord t.1 (cornerOffset a)=teeth k (sideRow t.1 a) := by
        apply Fin.ext; change 3*t.1.val+3*a.val=3*(t.1.val+a.val); omega
      rw [eq]; rfl

theorem sum_balance {k} [NeZero k] (F : Finset (Site k)) (T : Array Terms) (i : Nat) :
    (∑ p : FacePos k, coeff i (tile T p (faceMask F p))) =
      ∑ t : Fin 8 × J k × J k, coeff i (arc T k t.2.1 t.2.2 (stateAt F t.1 t.2.1 t.2.2)
        (stateAt F t.1 t.2.1 (t.2.2.val+1))) := by
  let f (g : Fin 8) (p : FacePos k) (a : Fin 2) := coeff i
    (stamp T k p.1 p.2 a (FaceLines.stepWord (stateAt F g (sideRow p.1 a) (p.2.val+1))
      (stateAt F g (sideRow p.1 a) (p.2.val+2))))
  simp only [tile,finCoeff,word_eq]
  rw [sum_comm,Fintype.sum_prod_type (fun t : Fin 8 × J k × J k => _)]
  apply sum_congr rfl; intro g _
  change (∑ p : FacePos k, ∑ a, f g (small k g p) a)=_
  have bij := Finite.injective_iff_bijective.mp (Function.LeftInverse.injective (Incidence.inverse (n:=k) g))
  trans ∑ p, ∑ a, f g p a
  · exact (Equiv.ofBijective (small k g) bij).sum_comp (fun p => ∑ a, f g p a)
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  have splitRow (j : Fin k) :
      (∑ r : J k, coeff i (arc T k r j.succ (stateAt F g r j.succ.val)
        (stateAt F g r (j.succ.val+1)))) =
      ∑ r : Fin k, (f g (r,j) 0 + f g (r,j) 1) := by
    simp only [arc,Fin.val_succ,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel,coeff_append]
    rw [sum_add_distrib,sum_add_distrib]
    congr 1
    · rw [Fin.sum_univ_castSucc]
      simp [coeff,f,sideRow]
      rfl
    · rw [Fin.sum_univ_succ]
      simp [coeff,f,sideRow]
      rfl
  rw [sum_comm (f:=fun (r j : J k) => _),Fin.sum_univ_succ]
  have zero (r : J k) (s t : State) : arc T k r 0 s t=[] := rfl
  simp only [Fin.val_zero,zero,show coeff i []=0 from rfl,sum_const_zero,zero_add]
  simp only [splitRow,Fin.sum_univ_two]
  rw [sum_comm]

end GridGraphs.NoPitch.TailRows.FaceLine
