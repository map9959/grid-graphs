import GridGraphs.ResidueTwoUpper.Opposite0101.Columns
import GridGraphs.ResidueTwoUpper.Opposite0101.Prices

namespace GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
open ResidueZero Stencil TwoGap.Words BoundarySix.Connected

private theorem seam : ∀ (v : Bool) (r : Fin 5), pTab v 14 r=pTab v 17 r := by native_decide

theorem physicalStrip {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) (canon : packed (signature (by omega) F)=code4 0 1 0 1)
    (v : Bool) : StripOK v u (cols F v) := by
  have prices := prices_of_score F acy score two
  refine ⟨small_col F v,fun j hj => colOK_physical F acy score canon v j hj,?_⟩
  intro j hj
  change localOK v (idx u j) (prev F v j) (cols F v j) (next F v j)=true
  simp only [localOK,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq]
  constructor
  · intro r hr
    rw [nb_physical _ _ _ _ hr hj,read_col _ _ _ _ (by omega)]
    let x := vertex v r j (by omega) hj
    have c : point v r j=coord x := by cases v <;> rfl
    rw [c,marked_at]
    exact star_entry_physical prices v r j hr hj
  · by_cases z : j=0
    · left; left; simp [idx,z]
    by_cases end' : j+1=35+42*u
    · left; right; unfold idx; split_ifs <;> omega
    right; intro r hr
    rw [mask_physical _ _ _ _ hr (by omega) (by omega) (by omega)]
    have id : j-1+1=j := by omega
    have eq : pTab v (idx u j-1) r=pTab v (idx u (j-1)) r := by
      rcases (idx_pair (u:=u) (j:=j-1) (by omega)).2 with a|⟨a,b⟩
      · rw [id] at a; rw [a,Nat.add_sub_cancel]
      · rw [id] at b; rw [a,b]; exact seam v ⟨r,hr⟩
    rw [eq]; exact patch_entry_physical prices _ _ _ hr (by omega)

/-- No physical square of exceptional size, including 35 and 77, with
the normalized opposite gaps can attain the putative upper value. -/
theorem exclude {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) : packed (signature (by omega) F)≠code4 0 1 0 1 :=
  fun canon => no_strips (physicalStrip F acy score two canon false)
    (physicalStrip F acy score two canon true) (shared F)

theorem adjacent_witness {u} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (two : (perimeterHoles F).card=2) :
    ∃ M : Finset (GridVertex (35+42*u) (35+42*u)), (Bonds M).IsAcyclic ∧
      M.card=440+1020*u+588*u^2 ∧ (perimeterHoles M).card=2 ∧
      packed (signature (by omega) M)=code4 0 0 1 1 := by
  obtain ⟨M,a,s,t,w⟩ := TwoGap.Exchange.canonical_witness F acy score two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at w
  exact ⟨M,a,s,t,w.resolve_right (exclude M a s t)⟩

end GridGraphs.ResidueTwoUpper.Exceptional.Opposite0101
