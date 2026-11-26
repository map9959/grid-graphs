import GridGraphs.NoPitch.TailRows.LineTransport

namespace GridGraphs.NoPitch.TailRows
open PitchCut Budget Finset

/-- In each orientation there are three individual junction bands on
either side and one interior band containing every other slot. -/
def mass (k a : Nat) : Nat :=
  if a=9 then k-5 else if a∈([0,3,6,12,15,18] : List Nat) then 1 else 0

private theorem band_cases (k j : Nat) (hk : 19≤k) (hj : j≤k) :
    band k j=if j=0 then 0 else if j=1 then 3 else if j=2 then 6 else
      if j=k then 18 else if j=k-1 then 15 else if j=k-2 then 12 else 9 := by
  simp only [band,Keys.axis,N]; split_ifs <;> omega

private theorem middle (k n : Nat) (hk : 19≤k) (hn : n≤k) :
    band k n=9 ↔ 3≤n ∧ n≤k-3 := by
  rw [band_cases k n hk hn]; split_ifs <;> constructor <;> intro h <;> first | contradiction | omega

private def endpoint (k a : Nat) := if a=0 then 0 else if a=3 then 1 else if a=6 then 2 else
  if a=12 then k-2 else if a=15 then k-1 else k

private theorem edge (k n a : Nat) (hk : 19≤k) (hn : n≤k)
    (mem : a∈([0,3,6,12,15,18] : List Nat)) : band k n=a ↔ n=endpoint k a := by
  rw [band_cases k n hk hn]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [endpoint] <;>
    split_ifs <;> constructor <;> intro h <;> first | exact Classical.byContradiction h | contradiction | omega

theorem band_fibre (k a : Nat) (hk : 19≤k) :
    (univ.filter (fun j : J k => band k j=a)).card=mass k a := by
  have hist (b : Nat) (hb : b≤k) :
      (univ.filter (fun j : J k => j.val=b)).card=1 := by
    let z : J k := ⟨b,by omega⟩
    have eq (j : J k) : j.val=b ↔ j=z := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    have e : (univ.filter (fun j : J k => j.val=b))={z} := by ext; simp [eq]
    rw [e,card_singleton]
  have mid : (univ.filter (fun j : J k => 3≤j.val ∧ j.val≤k-3)).card=k-5 := by
    let f (j : Fin (k-5)) : J k := ⟨j.val+3,by have := j.isLt; omega⟩
    have eq : (univ.filter (fun j : J k => 3≤j.val ∧ j.val≤k-3))=univ.image f := by
      ext j; simp only [mem_filter,mem_univ,true_and,mem_image]
      constructor
      · intro h; exact ⟨⟨j.val-3,by omega⟩,Fin.ext (by dsimp [f]; omega)⟩
      · rintro ⟨x,rfl⟩; have := x.isLt; dsimp [f]; omega
    have inj : Function.Injective f := by intro a b h; apply Fin.ext; have := congrArg Fin.val h; dsimp [f] at this; omega
    rw [eq,card_image_of_injective _ inj]; simp
  by_cases c : a=9
  · subst a
    have eq (j : J k) := middle k j.val hk (by omega)
    simpa only [eq,mass,if_true] using mid
  by_cases outside : a∈([0,3,6,12,15,18] : List Nat)
  · simp only [mass,if_neg c,if_pos outside]
    have hb : endpoint k a≤k := by unfold endpoint; split_ifs <;> omega
    have eq (j : J k) := edge k j.val a hk (by omega) outside
    simpa only [eq] using hist _ hb
  · have no (j : J k) : ¬band k j=a := by
      rw [band_cases _ _ hk (by omega)]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at outside
      split_ifs <;> omega
    simp [no,mass,c,outside]

theorem slot_histogram (k r j : Nat) (hk : 19≤k) :
    (univ.filter (fun p : J k × J k => band k p.1=r ∧ band k p.2=j)).card=mass k r*mass k j := by
  have eq : (univ.filter (fun p : J k × J k => band k p.1=r ∧ band k p.2=j))=
      (univ.filter (fun p : J k => band k p=r)).product (univ.filter (fun p : J k => band k p=j)) := by
    ext; simp
  rw [eq]; exact (card_product ..).trans (congrArg₂ (·*·) (band_fibre k r hk) (band_fibre k j hk))

end GridGraphs.NoPitch.TailRows
