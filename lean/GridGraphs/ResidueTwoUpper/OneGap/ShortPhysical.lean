import GridGraphs.ResidueTwoUpper.OneGap.ShortArrows
import GridGraphs.ResidueTwoUpper.OneGap.ShortSeed

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero Stencil L7 FanSlab GridGraphs.ResidueTwoUpper.Exceptional.Frame
variable {u : Nat}
local notation "N" => 35+42*u

private theorem skin_physical {F : Finset (GridVertex N N)} {P w q} (S : Seed F P w q)
    (r c : Nat) (hr : r<N-2) (hc : c<N-2) :
    frameOK N r c (maskAt F (origin r c hr hc)) := by
  apply List.all_eq_true.mpr; intro i _
  let x : GridVertex N N := (⟨r+i.val/3,by have := i.isLt; omega⟩,⟨c+i.val%3,by omega⟩)
  have X : coord x=((r:Int),(c:Int))+offset i := by ext <;> simp [coord,x,offset]
  have h := patch_bit F r c (by omega) (by omega) i
  change bit (maskAt F (origin r c hr hc)) i=(marked F (((r:Int),(c:Int))+offset i)).toNat at h
  rw [←X,marked_at] at h; simp only [h]
  have g := star_geometry (by omega : 35≤N) F P S.step x (S.good (.inl x))
  unfold skin; dsimp only; split
  · rename_i bd
    have D : depthAt N (coord x)=1 := by
      unfold depthAt depth; simp only [coord,x]; push_cast; omega
    simp [g.2.1 D]
  · split
    · rename_i bd
      have D : straight N (coord x) := by
        unfold straight depthAt depth; simp only [coord,x]; push_cast; constructor <;> omega
      simp [g.1 D]
    · rfl

private theorem wall_physical {F : Finset (GridVertex N N)} {P w q} (S : Seed F P w q)
    (r c : Nat) (hr : r<N-2) (hc : c<N-2) :
    wallOK N r c (maskAt F (origin r c hr hc)) (outDir (site r c hr hc) (P (site r c hr hc))) := by
  apply List.all_eq_true.mpr; intro d _
  by_cases z : wall N r c d
  swap
  · simp [Bool.eq_false_iff.mpr z]
  simp only [z,Bool.not_true,Bool.false_or,beq_iff_eq]
  let a := site r c hr hc
  have wrap : inside N (shift (center r c) d) := by
    fin_cases d <;> simp [shift,center,inside] <;> omega
  let b := onSite (shift (center r c) d) wrap
  have B : coord b=shift (center r c) d := coord_onSite ..
  have g : (gridGraph N N).Adj a b ∧ outDir a b=d.val := by
    have R := congrArg Prod.fst B; have C := congrArg Prod.snd B
    change adjacent _ _ _ _ ∧ _
    fin_cases d <;> norm_num [adjacent,coord,shift,center,site,a,Fin.ext_iff,outDir,Prod.ext_iff,Fin.lt_def] at R C ⊢ <;>
      constructor <;> (try split_ifs) <;> omega
  have bd : depthAt N (coord b)=0 := by simpa only [B,wall,beq_iff_eq] using z
  have nb : coord b≠L7.view w N 2 (2+3*q:Nat) := by
    intro eq; rw [eq] at bd; have := S.room
    cases w with | mk x y t => cases x <;> cases y <;> cases t <;>
      simp [depthAt,depth,L7.view,reflect] at bd <;> omega
  have ne : P b≠a := by
    intro eq
    have high := ((star_geometry (by omega : 35≤N) F P S.step b (S.good (.inl b))).2.2.1 bd).mpr
    have inward' : inward P b := by
      refine ⟨bd,?_⟩; rw [eq]
      rw [B] at bd; fin_cases d <;>
        simp [depthAt,depth,coord,center,shift,site,a] at bd ⊢ <;> omega
    have h := high inward'; rw [S.zero b nb] at h; exact absurd h (by decide)
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq,contact_iff F r c hr hc d B]
  change outDir a (P a)=d.val ↔ a∈F ∨ b∈F
  rw [←g.2,dir_eq F S.step g.1]
  exact ⟨fun h => h ▸ (S.step a (fun eq => g.1.ne (eq.symm.trans h))).2,
    fun m => (S.owners a b ⟨g.1,m⟩).mpr ne⟩

private theorem label_geo (w : View) (r c : Nat) (hr : r<N-2) (hc : c<N-2) :
    let t := unview w (N-2) r c
    t.1<N-2 ∧ t.2<N-2 ∧ L7.view w ((N:Nat):Int) (t.1+1:Nat) (t.2+1:Nat)=center r c ∧
      L7.view w (((N:Nat):Int)-2) t.1 t.2=((r:Int),(c:Int)) := by
  cases w with | mk x y t => cases x <;> cases y <;> cases t <;>
    simp [unview,L7.view,reflect,center,Prod.ext_iff] <;> omega

set_option maxHeartbeats 1500000 in
theorem kept_physical {F : Finset (GridVertex N N)} {P w q} (S : Seed F P w q) (acy : (Bonds F).IsAcyclic) :
    Kept (N-2) (actual F P) (planted N q w (localBoard N)) := by
  intro r hr c hc
  let a := origin r c hr hc; let x := site r c hr hc
  let m := maskAt F a; let o := outDir x (P x)
  let t := unview w (N-2) r c
  obtain ⟨R,C,E,H⟩ := label_geo w r c hr hc
  change L7.view w _ (t.1+1:Nat) (t.2+1:Nat)=coord x at E
  change L7.view w _ t.1 t.2=coord a at H
  obtain ⟨mark,nb⟩ := PatchFilter.packed_center F a x rfl
  have code : encode m w=square F w t.1 t.2 := (square_eq F w _ _ a H.symm).symm
  have pos : coord x=L7.view w N 2 (2+3*q:Nat) ↔ t=(1,1+3*q) := by
    rw [←E]; cases w with | mk f g k => cases f <;> cases g <;> cases k <;>
      simp [L7.view,reflect,Prod.ext_iff] <;> omega
  have seed : seedOK N q w r c m := by
    change (if t.1=1 ∧ t.2%3=1 then (if t.2<1+3*q then bit m 4==1 else
      encode (Fin.ofNat 512 m) w == (if t.2=1+3*q then 64 else 72)) else true)=true
    split
    swap
    · rfl
    rename_i aligned
    let j := t.2/3
    have J : t.2=1+3*j := by dsimp [j]; omega
    have W : coord x=L7.view w (N:Nat) 2 (2+3*j:Nat) := by
      simpa only [aligned.1,J,show 1+3*j+1=2+3*j by omega,
        show (((1+1:Nat):Int))=2 by decide] using E.symm
    split
    · rename_i pre
      have e := S.west j (by omega)
      rw [←W,marked_at] at e
      simp [m,mark,e]
    · rename_i post
      have mm : Fin.ofNat 512 m=m := Fin.ext (Nat.mod_eq_of_lt m.isLt)
      rw [mm,code,aligned.1,J]
      by_cases same : j=q
      · simp [same,S.paid]
      · have bound : j<11+14*u := by change t.2<N-2 at C; omega
        simp [same,S.east j (by omega) bound]
  rw [actual_at F P _ _ hr hc]
  change (m.val,o)∈_
  unfold planted; rw [at_build hr hc]
  by_cases same : t=(1,1+3*q)
  · rw [if_pos same]
    have O : o=4 := by simp [o,S.sink x (pos.mpr same),outDir]
    exact List.mem_map.mpr ⟨m.val,List.mem_filter.mpr ⟨List.mem_range.mpr m.isLt,seed⟩,by rw [O]⟩
  · rw [if_neg same]; apply List.mem_filter.mpr; refine ⟨?_,seed⟩
    unfold localBoard; rw [at_build hr hc]
    have raw := physical_mask_ok F acy r c (by omega) (by omega)
    have patch : patchPrice N r c m := Bool.and_eq_true_iff.mpr ⟨raw,beq_iff_eq.mpr (S.clean a)⟩
    have z := S.zero x (mt pos.mp same)
    have st := starOK_physical F acy x _ (fun h => S.step _ h.symm)
    have val : starPrice N r c (bit m 4) (PatchFilter.cnb m) o := by
      change bit m 4=_ at mark; change PatchFilter.cnb m=_ at nb
      rw [mark,nb]; exact Bool.and_eq_true_iff.mpr ⟨st,beq_iff_eq.mpr z⟩
    have b : PatchFilter.cnb m<16 := by rw [show PatchFilter.cnb m=_ from nb]; exact code_lt _
    apply List.mem_flatMap.mpr
    refine ⟨m.val,List.mem_filter.mpr ⟨List.mem_range.mpr m.isLt,Bool.and_eq_true_iff.mpr ⟨skin_physical S r c hr hc,patch⟩⟩,?_⟩
    apply List.mem_map.mpr; refine ⟨o,List.mem_filter.mpr ⟨?_,wall_physical S r c hr hc⟩,rfl⟩
    simp only [Vector.getElem_ofFn, Nat.mod_eq_of_lt b,Nat.mod_eq_of_lt (show bit m 4<2 from Nat.mod_lt _ (by decide)),
      List.mem_filter,List.mem_range]
    exact ⟨outDir_lt ..,val⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
