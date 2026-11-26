import GridGraphs.ResidueTwoUpper.OneGap.OddOccurrence

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero Stencil GridGraphs.ResidueTwoUpper.Exceptional.Frame BoundarySix.Connected Finset

/-- Distances are physical site coordinates; reflection preserves this
phase because `n-1 ≡ 4 (mod 6)`. -/
def arm (n a x : Int) : Prop := (a=2 ∨ a=n-3) ∧ 5≤x ∧ x+6≤n ∧ x%6=5
instance (n a x : Int) : Decidable (arm n a x) := by unfold arm; infer_instance

private theorem isolate_base : ∀ i j : Fin 35, let p : Pos := (i.val,j.val)
    twoOrbitStar 35 p 0 0 4=full → Parity.starBill 35 p 0 0 4%2=1 →
      arm 35 p.1 p.2 ∨ arm 35 p.2 p.1 := by native_decide

private theorem arms {u : Nat} {p : Pos} (inside' : inside (35+42*(u:Int)) p)
    (w : twoOrbitStar (35+42*(u:Int)) p 0 0 4=full)
    (odd : Parity.starBill (35+42*(u:Int)) p 0 0 4%2=1) :
    arm (35+42*(u:Int)) p.1 p.2 ∨ arm (35+42*(u:Int)) p.2 p.1 := by
  have h := reduced_inside 35 u (.inr rfl) (by positivity) p inside'
  let z := Parity.project 35 u p
  change inside 35 z at h
  simp only [inside,Bool.and_eq_true,decide_eq_true_eq] at h
  let i : Fin 35 := ⟨z.1.toNat,by omega⟩
  let j : Fin 35 := ⟨z.2.toNat,by omega⟩
  have e : ((i.val:Int),(j.val:Int))=z := Prod.ext (by dsimp [i]; omega) (by dsimp [j]; omega)
  have c := isolate_base i j
  dsimp only at c
  rw [e] at c
  rw [charges_star] at w
  rw [bit_star] at odd
  have dis := c w odd
  rw [show (i.val:Int)=z.1 from congrArg Prod.fst e,
    show (j.val:Int)=z.2 from congrArg Prod.snd e] at dis
  have lift (x y : Int) (ha : arm 35 (Parity.reduce 35 u x) (Parity.reduce 35 u y)) :
      arm (35+42*(u:Int)) x y := by
    unfold arm Parity.reduce at *
    split_ifs at ha <;> omega
  exact dis.elim (fun h => Or.inl (lift _ _ h)) (fun h => Or.inr (lift _ _ h))

def patchSite (u : Nat) (a : origins (35+42*u)) (m : Fin 512) : Prop :=
  let p := Parity.project 33 u (coord a)
  twoOrbitPatch 35 p m=full ∧ Parity.patchBill 35 p m%2=1 ∧ maskOK m

/-- A one-gap candidate's distinguished occurrence has odd price on the
actual forest. If it is a star, the center is physically isolated and the
longitudinal coordinate is `5 mod 6`; otherwise all star charges vanish
and the nine bits of the patch satisfy both reduced checks. -/
theorem defect_sites (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) :
    let n := 35+42*u
    ∃ P : GridVertex n n → GridVertex n n,
      (∀ x, P x≠x → (Bonds F).Adj x (P x)) ∧
      (∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) ∧ (∀ x, allGood F P x) ∧
      ((∃ v : GridVertex n n, (Bonds F).IsIsolated v ∧
          (arm n (coord v).1 (coord v).2 ∨ arm n (coord v).2 (coord v).1) ∧
          starSlack F P v=full ∧ ∀ x, x≠Sum.inl v → weightAt F P x=0) ∨
       (∃ a : origins n, 0<depthAt (n-2) (coord a) ∧ patchSite u a (maskAt F a) ∧
          patchSlack F a=full ∧ ∀ x, x≠Sum.inr a → weightAt F P x=0)) := by
  classical
  let n := 35+42*u
  have hn : 35≤n := by dsimp [n]; omega
  -- Retain the NW sink from the construction of `frame_of_score`, so the
  -- unaveraged parity certificate applies to precisely this orientation.
  obtain ⟨P,sink,step,arr,only,d,wd,zero⟩ := single_defect u F acy score
  have corners := corners_marked u F acy score
  have good := frame_checked stars_checked patches_checked u F P acy step corners (fun x => by
    by_cases eq : x=d
    · exact Or.inr (eq ▸ wd)
    · exact Or.inl (zero x eq))
  have gap := gap_split hn F P ⟨nw u,Or.inl rfl⟩ corners
    (fun _ _ e => (all_active_reachable u F acy score e).1) sink step arr good d zero
  have exits := (gap.resolve_right (fun h => by omega)).2
  have odd := odd_at_defect u F acy P sink only step arr d zero
  refine ⟨P,step,arr,good,?_⟩
  cases d with
  | inl v =>
    change starSlack F P v=full at wd
    have geo := star_geometry hn F P step v (good (.inl v))
    have notBd : depthAt n (coord v) ≠ 0 := by
      intro bd
      have iw := ((geo.2.2.1 bd).mp wd).2
      let x : PerimeterVertex n := ⟨v,(boundary_iff _).mpr bd⟩
      have hx : x∈exitSet P := mem_filter.mpr ⟨mem_univ _,fun h => by
        have eq := (boundary_iff _).mp h
        change depthAt n (coord (P v))=0 at eq
        omega⟩
      rw [exits] at hx
      exact notMem_empty _ hx
    obtain ⟨_,unmarked,nb,fix⟩ := geo.2.2.2 ⟨notBd,wd⟩
    have empty : (Bonds F).IsIsolated v := by
      intro w edge
      have markedW := edge.2.resolve_left unmarked
      let dir : Fin 4 := ⟨outDir v w,by
        have ne := edge.1.ne
        unfold outDir; rw [if_neg ne]; split_ifs <;> decide⟩
      have b := neighbours_bit F (coord v) dir
      change w∈F at markedW
      rw [nb,show shift (coord v) dir=coord w from shift_out edge.1,marked_at] at b
      simp [bit,markedW] at b
    have e : (n:Int)=35+42*(u:Int) := by dsimp [n]
    change Parity.starBill n (coord v) _ _ _ %2=1 at odd
    have dir : outDir v (P v)=4 := by simp [fix,outDir]
    unfold starSlack at wd
    simp only [unmarked,decide_false,Bool.toNat_false,nb,dir] at wd odd
    refine Or.inl ⟨v,empty,?_,?_,zero⟩
    · rw [e]; exact arms (e ▸ coord_inside v) (e ▸ wd) (e ▸ odd)
    · simpa [starSlack,unmarked,nb,dir] using wd
  | inr a =>
    change patchSlack F a=full at wd
    have e : (n:Int)=35+42*(u:Int) := by dsimp [n]
    change Parity.patchBill n (coord a) _ %2=1 at odd
    have w : twoOrbitPatch n (coord a) (maskAt F a)=full := wd
    rw [e,charges_patch] at w
    rw [e,bit_patch] at odd
    exact Or.inr ⟨a,(patch_geometry hn F P a (good (.inr a))).1 wd,
      ⟨w,odd,physical_mask_ok F acy ..⟩,wd,zero⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
