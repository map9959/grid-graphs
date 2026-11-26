import GridGraphs.NoPitch.FaceLineRows

namespace GridGraphs.NoPitch.FaceLines
open GridGraphs.NoPitch.Dual Keys PitchCut FaceRows Finset

def startAt (F : Finset (Site 6)) (g : Fin 8) (z : Slot) :=
  prefixState (view F g) (teeth 6 z.1) z.2.val
def stopAt (F : Finset (Site 6)) (g : Fin 8) (z : Slot) :=
  prefixState (view F g) (teeth 6 z.1) (z.2.val+1)
def wordAt (F : Finset (Site 6)) (g : Fin 8) (z : Slot) :=
  stepWord (startAt F g z) (stopAt F g z)
def number (w : EdgeWord) := (w 0).toNat + 2*(w 1).toNat + 4*(w 2).toNat + 8*(w 3).toNat

private theorem rotated_bit (F : Finset (Site 6)) (g : Fin 8) (p : Pos) (a : Fin 2) (b : Fin 4) :
    let q := small 4 (invers g) (cornerOffset a,b)
    faceMask F p q.1 q.2=faceMask (view F g) (rotPos g p) (cornerOffset a) b := by
  let q := small 4 (invers g) (cornerOffset a,b)
  let x : Site 6 := (coord p.1 q.1,coord p.2 q.2)
  have transport : ∀ (g : Fin 8) (p : Pos) (a : Fin 2) (b : Fin 4),
      let q := small 4 (invers g) (cornerOffset a,b)
      small 19 g (coord p.1 q.1,coord p.2 q.2) =
        (coord (rotPos g p).1 (cornerOffset a),coord (rotPos g p).2 b) := by decide +kernel
  have inv : ∀ (g : Fin 8) (y : Site 6), small 19 (invers g) (small 19 g y)=y := by decide +kernel
  apply Bool.eq_iff_iff.mpr
  simp only [faceMask,decide_eq_true_eq,←transport g p a b]
  constructor
  · exact mem_image_of_mem _
  · intro h; obtain ⟨y,m,e⟩ := mem_image.mp h
    exact (Function.LeftInverse.injective (inv g) e) ▸ m

theorem word_same (F : Finset (Site 6)) (g : Fin 8) (p : Pos) (a : Fin 2) :
    rotWord g (faceMask F p) a=wordAt F g (pointSlot (rotPos g p) a) := by
  let S := view F g
  let t := rotPos g p
  calc
    _ = number (faceMask S t (cornerOffset a)) := by
      unfold rotWord
      simp only [List.range_succ,List.range_zero,List.foldl_append,List.foldl_cons,List.foldl_nil,
        rotated_bit]
      change 0 + _ * 1 + _ * 2 + _ * 4 + _ * 8 = _ + 2*_ + 4*_ + 8*_
      ring_nf
      rfl
    _ = number (lineEdge S (coord t.1 (cornerOffset a)) t.2) := by rw [edge_agrees]
    _ = _ := by
      have eq : coord t.1 (cornerOffset a)=teeth 6 (pointSlot t a).1 := by
        apply Fin.ext; change 3*t.1.val+3*a.val=3*(t.1.val+a.val); omega
      rw [eq]; rfl

private theorem coeff_flat {A : Type*} (i : Nat) (f : A → Terms) (l : List A) :
    coeff i (l.flatMap f)=(l.map fun x => coeff i (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [coeff,List.flatMap_cons] at ih ⊢; exact ih

private theorem coeff_range (i : Nat) {n} (f : Fin n → Terms) :
    coeff i ((List.finRange n).flatMap f)=∑ j, coeff i (f j) := by
  rw [coeff_flat,←List.sum_toFinset _ (List.nodup_finRange n)]
  simp

theorem physical_balance (F : Finset (Site 6)) (i : Nat) :
    (∑ p : Pos, coeff i (rotStamps (faceMask F p) p)) =
    ∑ t : Fin 8 × Slot, coeff i (lineStamps t.2 (startAt F t.1 t.2) (stopAt F t.1 t.2)) := by
  let f (g : Fin 8) (e : Pos × Fin 2) := coeff i
    (stamp e.1 e.2 (wordAt F g (pointSlot e.1 e.2)))
  have fibres : ∀ z : Slot, (around z).Nodup ∧ (around z).toFinset =
      univ.filter (fun e : Pos × Fin 2 => pointSlot e.1 e.2=z) := by decide +kernel
  have arc (g : Fin 8) (z : Slot) :
      coeff i (lineStamps z (startAt F g z) (stopAt F g z)) =
        ∑ e ∈ univ.filter (fun e : Pos × Fin 2 => pointSlot e.1 e.2=z), f g e := by
    rw [lineStamps,coeff_flat,←List.sum_toFinset _ (fibres z).1,(fibres z).2]
    apply sum_congr rfl; rintro ⟨p,a⟩ he
    simp only [f,(mem_filter.mp he).2,wordAt]
  have bij (g : Fin 8) : Function.Bijective (rotPos g) := by
    have h : ∀ (g : Fin 8) (p : Pos), rotPos (invers g) (rotPos g p)=p := by decide +kernel
    exact Finite.injective_iff_bijective.mp (Function.LeftInverse.injective (h g))
  simp only [rotStamps,coeff_range,word_same]
  rw [Fintype.sum_prod_type (fun t : Fin 8 × Slot =>
    coeff i (lineStamps t.2 (startAt F t.1 t.2) (stopAt F t.1 t.2)))]
  simp only [arc]
  rw [sum_comm]
  apply sum_congr rfl; intro g _
  rw [sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) (f g),Fintype.sum_prod_type (f g)]
  exact (Equiv.ofBijective (rotPos g) (bij g)).sum_comp (fun p => ∑ a, f g (p,a))

end GridGraphs.NoPitch.FaceLines
