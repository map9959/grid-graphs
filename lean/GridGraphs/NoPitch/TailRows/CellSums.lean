import GridGraphs.NoPitch.TailRows.AdjacencySums

namespace GridGraphs.NoPitch.TailRows.Incidence
open PitchCut Keys Budget LocalBoard19 Finset GridGraphs.NoPitch.Dual
variable {k : Nat}
theorem turn_site [NeZero (N k-2)] (g : Fin 8) (p : PatchPos k) (q : Q) :
    small (N k) g (atSite p q)=atSite (small (N k-2) g p) (small 3 g q) := by
  have a := pos g (atSite p q); have b := pos g p; have c := pos g q
  have nk : N k=3*k+1 := rfl
  have := p.1.isLt; have := p.2.isLt; have := q.1.isLt; have := q.2.isLt
  apply Prod.ext <;> apply Fin.ext <;> fin_cases g <;> simp [atSite,transform,Prod.ext_iff] at a b c ⊢ <;> omega

theorem cell_word (F : Finset (Site k)) (p : PatchPos k) (q : Q) (g : Fin 8) :
    cellWord (small 3 g q) ((patchMask F p) q) (patchBits (patchMask F p) q g)=
    cellWord (small 3 g q) (decide (atSite p q∈F)) (rotatedBits (bitsAt F (atSite p q)) g) := by
  have loc : ∀ (q : Q) (g : Fin 8) (d : Fin 4) (z : Q), localQ (small 3 g q) d=some z →
      let a := small 3 (invers g) z; let v := dirView (invers g) d
      (a.1.val:Int)=q.1.val+dr v ∧ (a.2.val:Int)=q.2.val+dc v := by decide +kernel
  have eq (d : Fin 4) (m : (localQ (small 3 g q) d).isSome) :
      patchBits (patchMask F p) q g d=rotatedBits (bitsAt F (atSite p q)) g d := by
    cases h : localQ (small 3 g q) d with
    | none => simp [h] at m
    | some z =>
      have s := loc q g d z h
      have geom : probe (atSite p q) (dirView (invers g) d).val =some (atSite p (small 3 (invers g) z)) := by
        rw [←shift_probe,shift_iff]; dsimp only [atSite]; dsimp only at s; constructor <;> omega
      simp only [patchBits,h,rotatedBits,bitsAt,geom,Option.any_some,mask_at]
  have e := List.map_congr_left (l:=(List.finRange 4).filter fun d => (localQ (small 3 g q) d).isSome)
    (fun d hd => eq d (List.mem_filter.mp hd).2)
  unfold cellWord; dsimp only; rw [e,mask_at]

theorem cell_agree (hk : 19≤k) (B : Book) (F : Finset (Site k)) (p : PatchPos k) (q : Q) (g : Fin 8) :
    socketAt B (starFine (atSite p q)) q g (decide (atSite p q∈F)) (bitsAt F (atSite p q))=
    plugAt B (patchFine p) q g (patchMask F p) := by
  have n : 40≤N k-2 := by unfold N; omega
  haveI : NeZero (N k-2) := ⟨by omega⟩
  let a := small (N k-2) g p
  let z := small 3 g q
  let x := atSite a z
  have r := z.1.isLt; have c := z.2.isLt
  have u : (x.1.val:Int)=a.1.val+z.1.val := by simp [x,atSite]
  have v : (x.2.val:Int)=a.2.val+z.2.val := by simp [x,atSite]
  have h := (valid_eq x (r:= -(z.1.val:Int)) (c:= -(z.2.val:Int)) (m:=N k-2)
    (dn:= -2) (Or.inr rfl) (by omega) (by omega) (by omega)).2
    (by have := a.1.isLt; have := a.2.isLt; omega)
  rw [plugAt,cell_word,socketAt,patch_views]
  apply congrArg (fun key => lookup B.S key _)
  unfold socket plug starFine turn fineViews; rw [turn_site]
  change (if valid 8 (fine (N k) 8 x.1 x.2) _ _ _ then _ else _)=_
  rw [if_pos h]
  have s : (N k+8)%3=0 := by unfold N; omega
  have t : (N k-2+7)%3=0 := by unfold N; omega
  change some (eventKey (moved 8 (fine (N k) 8 x.1 x.2) _ _ _) (moved 8 (fine (N k) 8 x.1 x.2) _ _ _) _) =
    some (eventKey (moved 7 (fine (N k-2) 7 a.1 a.2) _ _ _) (moved 7 (fine (N k-2) 7 a.1 a.2) _ _ _) _)
  rw [moved_eq x a (r:= -(z.1.val:Int)) (c:= -(z.2.val:Int)) (dn:= -2) (Or.inr rfl) s (by omega) (by omega) (by omega) (by omega) (by omega),
    moved_eq x x (Or.inr rfl) s (by omega) (by omega) (by omega) (by omega) (by decide),
    moved_eq a a (Or.inl rfl) t n (by omega) (by omega) (by omega) (by decide),
    moved_eq a x (Or.inl rfl) t n u v (by omega) (by omega)]

theorem cell_absent (hk : 19≤k) (B : Book) (x : Site k) (q : Q) (g : Fin 8) (f bits)
    (no : ¬∃ p : PatchPos k, atSite p q=x) : socketAt B (starFine x) q g f bits=[] := by
  have n : 40≤N k-2 := by unfold N; omega
  haveI : NeZero (N k-2) := ⟨by omega⟩
  let z := small 3 g q
  let y := small (N k) g x
  have r := z.1.isLt; have c := z.2.isLt
  have h : ¬valid 8 (fine (N k) 8 y.1 y.2) (-(z.1.val:Int)) (-(z.2.val:Int)) (-2) := by
    intro v
    have a := (valid_eq y (m:=N k-2) (dn:= -2) (Or.inr rfl) (by omega) (by omega) (by omega)).mp v
    let p : PatchPos k := (⟨y.1.val-z.1.val,by omega⟩,⟨y.2.val-z.2.val,by omega⟩)
    have e : atSite p z=y := by apply Prod.ext <;> apply Fin.ext <;> dsimp [p,atSite] <;> omega
    have eq := congrArg (small (N k) (invers g)) e
    rw [turn_site] at eq
    apply no; exact ⟨_,by simpa only [y,z,inverse] using eq⟩
  unfold socketAt socket
  change lookup _ (if valid 8 (fine (N k) 8 y.1 y.2) _ _ _ then _ else none) _=[]
  rw [if_neg h]; rfl

def socketAmt (B : Book) (F : Finset (Site k)) (i : Nat) (x : Site k) (q : Q) :=
  ∑ g, coeff i (socketAt B (starFine x) q g (decide (x∈F)) (bitsAt F x))
def plugAmt (B : Book) (F : Finset (Site k)) (i : Nat) (p : PatchPos k) (q : Q) :=
  ∑ g, coeff i (plugAt B (patchFine p) q g (patchMask F p))
theorem cell_sum (hk : 19≤k) (B : Book) (F : Finset (Site k)) (i : Nat) :
    (∑ x, ∑ q, socketAmt B F i x q)=∑ p, ∑ q, plugAmt B F i p q := by
  rw [sum_comm (s:=univ (α:=Site k)),sum_comm (s:=univ (α:=PatchPos k))]
  apply sum_congr rfl; intro q _
  let e (p : PatchPos k) := atSite p q
  have inj : Function.Injective e := by
    intro a b h
    have r := congrArg (fun x : Site k => x.1.val) h; have c := congrArg (fun x : Site k => x.2.val) h
    dsimp [e,atSite] at r c
    apply Prod.ext <;> apply Fin.ext <;> omega
  have z : ∑ x, socketAmt B F i x q=∑ x ∈ univ.image e, socketAmt B F i x q := by
    symm; apply sum_subset (subset_univ _); intro x _ no; apply sum_eq_zero; intro g _
    rw [cell_absent hk B x q g _ _ (by simpa [e] using no)]; rfl
  rw [z,sum_image inj.injOn]; simp only [e,socketAmt,plugAmt,cell_agree hk]
end GridGraphs.NoPitch.TailRows.Incidence
