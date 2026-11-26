import GridGraphs.NoPitch.TailRows.FaceLineChecks
import GridGraphs.Tests.FaceCoverage19

namespace GridGraphs.NoPitch.TailRows.FaceLine
open PitchCut Keys FaceRows Wired Budget LocalBoard19 GridGraphs.NoPitch.Dual

private def squash {k} (x : Fin k) : Fin 3 :=
  if x.val=0 then 0 else if x.val+1=k then 2 else 1

private theorem squash_turn {k} [NeZero k] (hk : 3≤k) (p : FacePos k) (g : Fin 8) :
    let q := small k g p
    let t := small 3 g (squash p.1,squash p.2)
    (axisLabel k q.1,axisLabel k q.2)=(axisLabel 3 t.1,axisLabel 3 t.2) := by
  have ax (x : Fin k) : axisLabel k x=axisLabel 3 (squash x) ∧
      axisLabel k (k-1-x.val)=axisLabel 3 (2-(squash x).val) := by
    have := x.isLt
    by_cases lo : x.val=0
    · simp [squash,lo,axisLabel,show k-1≠0 by omega,Nat.sub_add_cancel (by omega : 1≤k)]
    · by_cases hi : x.val+1=k
      · simp [squash,lo,hi,axisLabel,show k-1-x.val=0 by omega]
      · simp [squash,lo,hi,axisLabel,show k-1-x.val≠0 by omega,show k-1-x.val+1≠k by omega]
  have h := Incidence.pos g p
  have w := Incidence.pos g (squash p.1,squash p.2)
  have := p.1.isLt; have := p.2.isLt; have := (squash p.1).isLt; have := (squash p.2).isLt
  dsimp only
  fin_cases g <;> norm_num [transform,Prod.ext_iff] at h w ⊢ <;>
    rw [h.1,h.2,w.1,w.2] <;> simp only [Nat.sub_sub_self (by omega : p.2.val≤k-1),
      Nat.sub_sub_self (by omega : (squash p.2).val≤2), (ax _).1,(ax _).2,true_and]

private theorem key_form {k} [NeZero k] (hk : 3≤k) (p : FacePos k) (vs : Vector Nat 8) :
    keyAt p vs=8*(minimum fun g =>
      let q := small k g p
      pack [axisLabel k q.1,axisLabel k q.2]*16777216+vs[g])+2 := by
  have ax (x : Fin k) : axis (N k-3) 2 (3*x.val)=axisLabel k x := by
    have := x.isLt; unfold axis N axisLabel; split_ifs <;> omega
  have scaled (g : Fin 8) : transform g (N k-3) (3*p.1.val) (3*p.2.val)=
      (3*(small k g p).1.val,3*(small k g p).2.val) := by
    have h := Incidence.pos g p
    have := p.1.isLt; have := p.2.isLt
    fin_cases g <;> norm_num [N,transform,Prod.ext_iff] at h ⊢ <;> omega
  simp only [keyAt,scaled,ax]

theorem physical_tile {k} [NeZero k] (hk : 3≤k) (w : Nat → Terms) (T : Array Terms)
    (ok : tilesOK w T) (F : Finset (Site k)) (acy : (Wired.G F).IsAcyclic) (p : FacePos k) :
    balanced (w (face F p) ++ negTerms (tile T p (faceMask F p))) := by
  let u : FacePos 3 := (squash p.1,squash p.2)
  have same (g : Fin 8) := squash_turn hk p g
  change ∀ g, _ at same
  have key (vs : Vector Nat 8) : keyAt p vs=keyAt u vs := by
    rw [key_form hk,key_form (by decide : 3≤3)]
    simp only [u,(Prod.mk.inj (same _)).1,(Prod.mk.inj (same _)).2]
  have stamps (m : Mask) : tile T p m=tile T u m := by
    simp only [tile,stamp,u,(Prod.mk.inj (same _)).1,(Prod.mk.inj (same _)).2]
  let m := faceMask F p
  let q := (faceAtom F p).2
  obtain ⟨lt,mask⟩ := mask_roundtrip m
  obtain ⟨mem,part⟩ := partition_roundtrip q (physical_partition F p)
  obtain ⟨raw,yes⟩ := physical_wiring p F acy
  have cat : colorCode q∈catalog m := List.mem_filter.mpr ⟨mem,by rwa [part]⟩
  unfold tilesOK at ok; simp only [decide_eq_true_eq] at ok
  have all := ok ⟨_,lt⟩
  rw [mask] at all
  have pass := List.all_eq_true.mp (all raw) _ cat
  unfold positions at pass; simp only [decide_eq_true_eq] at pass
  have cover : ∀ p : FacePos 3, ∃ j : Fin 9, pos j=p := by decide
  obtain ⟨j,hj⟩ := cover u
  have h := pass j
  simp only [Fin.getElem_fin,Vector.getElem_ofFn,hj,part] at h
  change balanced (w (keyAt p (faceViews m q)) ++ negTerms (tile T p m))
  rwa [key,stamps]

private theorem label_rep {k b} (hb : 19≤b) (hk : b≤k) (j : Nat) (hj : j≤k) :
    let v := rep k b j
    axisLabel b v=axisLabel k j ∧ axisLabel b (v-1)=axisLabel k (j-1) := by
  dsimp only
  constructor <;> unfold rep axisLabel <;> split_ifs <;> omega

theorem physical_arc {k b} (hb : 19≤b) (hk : b≤k) (w : Nat → Terms) (T : Array Terms)
    (ok : arcOK b w T) (F : Finset (Site k)) (g : Fin 8) (r j : J k)
    (np : ¬Pitch (view F g) (teeth k r)) :
    let s := prefixState (view F g) (teeth k r) j.val
    let t := prefixState (view F g) (teeth k r) (j.val+1)
    balanced (w (line F g r j) ++ arc T k r j s t) := by
  obtain ⟨hs,pass⟩ := physical_step _ _ np j
  have R := rep_geometry hb hk (j:=r.val) (by omega)
  have C := rep_geometry hb hk (j:=j.val) (by omega)
  let u : J b := ⟨rep k b r,by omega⟩
  let v : J b := ⟨rep k b j,by omega⟩
  have fr : u.val=0 ↔ r.val=0 := R.2.1
  have lr : u.val<b ↔ r.val<k := by have := R.2.2.1; dsimp [u]; omega
  have fj : v.val=0 ↔ j.val=0 := C.2.1
  have lj : v.val=b ↔ j.val=k := C.2.2.1
  have clip : min v.val 4=min j.val 4 := C.2.2.2.1
  have same (s a) : permit b v.val s a=permit k j.val s a := by
    have f : (v.val==0)=(j.val==0) := Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using fj)
    have l : (v.val==b)=(j.val==k) := Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using lj)
    simp only [permit,bne,f,l]
  have eqArc (s t) : arc T b u v s t=arc T k r j s t := by
    have ar := label_rep hb hk r.val (by omega)
    have aj := label_rep hb hk j.val (by omega)
    simp only [arc,stamp,fj,lr,fr,u,v,ar.1,ar.2,aj.2]
  unfold arcOK at ok; simp only [decide_eq_true_eq] at ok
  have h := ok u v _ (clip ▸ hs) _ ((same ..) ▸ pass)
  have a : band b u=band k r := R.2.2.2.2.1
  have c : band b v=band k j := C.2.2.2.2.1
  have d : prior b v=prior k j := C.2.2.2.2.2
  rw [eqArc,a,c,d] at h
  simpa only [line,arcKey,band,prior,prefixState,show ((teeth k r).val)=3*r.val from rfl,
    show 3*j.val-3=3*(j.val-1) by omega] using h

end GridGraphs.NoPitch.TailRows.FaceLine
