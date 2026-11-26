import GridGraphs.ResidueTwoUpper.Star

namespace GridGraphs.ResidueTwoUpper.PhysicalCounts
open NoPitch.Dual NoPitch.Keys Location GridGraphs.ResidueTwoUpper.Star Finset

abbrev N (t : Nat) := 20+3*t
abbrev S (t : Nat) := 18+3*t
abbrev Forced {t} (F : Finset (Site (N t))) :=
  forcedEdgeGraph (gridGraph (N t) (N t)) (↑F : Set _)
abbrev root (t : Nat) : Site (N t) := (0,0)

private theorem reduced_inside {i j t} (hi : i<N t) (hj : j<N t) (d : Dir) :
    inside (N t) i j d ↔ inside 20 (rep (N t) 6 i) (rep (N t) 6 j) d := by
  exact and_congr (neighbor_matches (d:=6) (t:=t) (by decide) hi
    (show dr d≤2 by fin_cases d <;> decide)).1
    (neighbor_matches (d:=6) (t:=t) (by decide) hj
      (show dc d≤2 by fin_cases d <;> decide)).1

theorem reduced_key {t i j} (hi : i<N t) (hj : j<N t) (f b o) :
    key (N t) i j f (letter (N t) i j b) o =
      key 20 (rep (N t) 6 i) (rep (N t) 6 j) f (letter 20 (rep (N t) 6 i) (rep (N t) 6 j) b) o := by
  have letters : letter (N t) i j b=letter 20 (rep (N t) 6 i) (rep (N t) 6 j) b := by
    funext d; simp only [letter,reduced_inside hi hj]
  rw [letters]
  apply congrArg (fun z : Nat => 2*z)
  apply congrArg minimum
  funext g
  have m₁ := fine_matches (d:=6) (t:=t) hi
  have m₂ := fine_matches (d:=6) (t:=t) hj
  have r₁ := reflected_fine_matches (d:=6) (t:=t) hi
  have r₂ := reflected_fine_matches (d:=6) (t:=t) hj
  have bj : rep (N t) 6 j<20 := rep_valid (d:=6) (t:=t) hj
  have rev : 19+3*t-(19+3*t-j)=j := by unfold N at hj; omega
  have rev' : 19-(19-rep (N t) 6 j)=rep (N t) 6 j := by omega
  norm_num at r₁ r₂
  unfold encoding
  have loc : let p := transform g (N t) i j
             let q := transform g 20 (rep (N t) 6 i) (rep (N t) 6 j)
             Location.axis (N t) 6 p.1*16+Location.axis (N t) 6 p.2 =
               Location.axis 20 6 q.1*16+Location.axis 20 6 q.2 := by
    fin_cases g <;> simp [transform,N] <;> simp_all only [N,Nat.reduceMul,Nat.reduceAdd]
  dsimp only at loc ⊢
  rw [loc]

variable {t : Nat} (F : Finset (Site (N t))) (ac : (Forced F).IsAcyclic)
noncomputable def arrows := forestArrows (n:=N t) (by unfold N; omega) F ac (root t)
noncomputable def starKey (x : Site (N t)) := key (N t) x.1 x.2 (decide (x∈F))
  (letter (N t) x.1 x.2 (sample F x)) (out (arrows F ac) x)
def patchKey (x : Site (S t)) := PatchColumns.key (S t) x.1 x.2 (Patch.patchMask
  (a:=x.1.val) (b:=x.2.val) (by have := x.1.isLt; dsimp [S,N] at *; omega)
  (by have := x.2.isLt; dsimp [S,N] at *; omega) F)

theorem star_entry (x : Site (N t)) :
    ∃ j, locate periodThree (index periodThree) (starKey F ac x)=some j ∧
      periodThree.cols[j].objective*(periodThree.cols[j].units:Int) = if x∈F then 8 else 0 := by
  let f := decide (x∈F)
  let b := sample F x
  let o := out (arrows F ac) x
  have c : compatible (N t) x.1 x.2 f b o := physical_compatible _ ac _ _
  have cc : compatible 20 (rep (N t) 6 x.1) (rep (N t) 6 x.2) f b o := by
    simpa only [compatible,←reduced_inside x.1.isLt x.2.isLt] using c
  have h := base_checked
  unfold baseCheck at h
  have hit := of_decide_eq_true h
    ⟨_,rep_valid (d:=6) (t:=t) x.1.isLt⟩ ⟨_,rep_valid (d:=6) (t:=t) x.2.isLt⟩ f b o cc
  obtain ⟨j,found,ok⟩ := (Option.any_eq_true _ _).mp hit
  refine ⟨j,?_,?_⟩
  · unfold starKey; rw [reduced_key x.1.isLt x.2.isLt]; exact found
  · change (_ == if f then (8:Int) else 0) = true at ok
    simpa only [f,decide_eq_true_eq] using beq_iff_eq.mp ok

noncomputable def vector (j : Fin periodThree.cols.size) :=
  scatter periodThree (index periodThree) (starKey F ac) j +
    scatter periodThree (index periodThree) (patchKey F) j

theorem nonnegative (j : Fin periodThree.cols.size) : 0 ≤ vector F ac j := by
  unfold vector scatter; positivity

private theorem patch_zero : periodThree.cols.all (fun c => c.key%2!=1 || c.objective==0) := by
  native_decide

theorem scatter_sum {I : Type*} [Fintype I] {D : Chart} (ix : Index) (ks : I → Nat)
    (w : Fin D.cols.size → Int) (v : I → Int)
    (hw : ∀ i, ∃ j, locate D ix (ks i)=some j ∧ w j*(D.cols[j].units:Int)=v i) :
    ∑ j, w j*scatter D ix ks j = ∑ i, v i := by
  simp only [scatter,mul_sum]; rw [sum_comm]
  apply sum_congr rfl; intro i _
  obtain ⟨j,e,eq⟩ := hw i
  rw [sum_eq_single j]
  · simpa [e] using eq
  · intro b _ ne; simp [e,Ne.symm ne]
  · simp

theorem objective : score periodThree (vector F ac)=8*(F.card:Int) := by
  unfold score vector
  simp only [mul_add,sum_add_distrib]
  rw [scatter_sum _ _ _ (fun x => if x∈F then 8 else 0) (star_entry F ac)]
  have patch (x : Site (S t)) := PatchColumns.physical_patch_found
    (t:=t) x.1.isLt x.2.isLt F ac
  rw [scatter_sum _ _ _ (fun _ => 0)]
  · simp [mul_comm]
  · intro x
    obtain ⟨j,found⟩ := Option.isSome_iff_exists.mp (patch x)
    refine ⟨j,found,?_⟩
    have k := locate_key found
    have odd : periodThree.cols[j].key%2=1 := by rw [k]; unfold PatchColumns.key; omega
    have eq := Array.all_eq_true_iff_forall_mem.mp patch_zero _ (Array.getElem_mem j.isLt)
    change (periodThree.cols[j].key%2!=1 || periodThree.cols[j].objective==0)=true at eq
    have zero : periodThree.cols[j].objective=0 := by simpa only [odd,bne_self_eq_false,
      Bool.false_or,beq_iff_eq] using eq
    rw [zero,zero_mul]

end GridGraphs.ResidueTwoUpper.PhysicalCounts
