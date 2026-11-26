import GridGraphs.ResidueTwoUpper.TwoGapFrontierAdvance

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph Finset ResidueZero Stencil BoundarySix.Connected Catalogue Words
open scoped Sym2

variable {u : Nat}
def rowSite (u l t : Nat) (i : Fin 9) : Board u := (Fin.ofNat (Size u) t,Fin.ofNat (Size u) (l+i.val))
def rootPort (u l t : Nat) (i : Fin 10) : Board u :=
  if i.val<9 then rowSite u l t (Fin.ofNat 9 i.val) else nw u
def rowPort (u l t : Nat) (i : Fin 19) : Board u :=
  if i.val<10 then rootPort u l t (Fin.ofNat 10 i.val) else rowSite u l (t+1) (Fin.ofNat 9 (i.val-10))
def events (F : Finset (Board u)) (l : Nat) (d : Fin 2) (x : Board u) : Prop :=
  if d=0 then x=nw u ∨ (0<x.1.val ∧ (x.2.val=l ∨ x.2.val=l+8)) else x∈F ∧ 0<x.1.val ∧ x≠nw u
instance {l t} (v : Board u) : Decidable (prefixBox l t v) := by unfold prefixBox; infer_instance
def pinsTo (F : Finset (Board u)) (d l t : Nat) := (pinSet F d).filter fun x => prefixBox l t x

def built (F : Finset (Board u)) (d l t : Nat) :=
  pinned (prefixGraph F l t) (nw u) (pinsTo F d l t)

theorem built_adj {F : Finset (Board u)} {d l t} {x y : Board u} :
    (built F d l t).Adj x y ↔
    ((Bonds F).Adj x y ∧ ¬IsGridBoundary x ∧ ¬IsGridBoundary y ∧ prefixBox l t x ∧ prefixBox l t y) ∨
    (x=nw u ∧ y∈pinSet F d ∧ prefixBox l t y ∧ x≠y) ∨
    (y=nw u ∧ x∈pinSet F d ∧ prefixBox l t x ∧ x≠y) := by
  classical
  simp only [built,pinned,sup_adj,iSup_adj,edge_adj,pinsTo,mem_filter]
  change (((_ ∧ _ ∧ _) ∧ ¬¬_ ∧ ¬¬_) ∨ _) ↔ _
  simp only [not_not]
  grind

theorem built_box {F : Finset (Board u)} {d l t} {x y : Board u}
    (h : (built F d l t).Adj x y) : (prefixBox l t x ∨ x=nw u) ∧ (prefixBox l t y ∨ y=nw u) := by
  rw [built_adj] at h; tauto

theorem built_escape (F : Finset (Board u)) {P d} (C : North.Chart F P d)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by unfold Size; omega) F)=code4 0 0 1 1)
    {l t : Nat} (lo : 3≤l) (hi : l+8+3≤high u) (ht : t+1<high u) :
    Escape (built F d l (t+1)) (rowPort u l t) (events F l) := by
  intro j x r mark
  change x∈F ∧ 0<x.1.val ∧ x≠nw u at mark
  let H := built F d l (t+1)
  have bx : prefixBox l (t+1) x ∨ x=nw u ∨ x.1.val=0 := by
    obtain ⟨w⟩ := r.symm
    cases w with
    | cons e _ => exact (built_box e).1.elim Or.inl (fun h => .inr (.inl h))
    | nil =>
      have J := j.isLt
      have B : l+j.val<Size u := by dsimp [Size,high] at *; omega
      have T : t<Size u := by dsimp [Size,high] at *; omega
      have eq : rowPort u l t ⟨j.val,by omega⟩=rowSite u l t j := by
        simp [rowPort,rootPort,J,show j.val<10 by omega,Fin.ofNat_eq_cast,Fin.ext_iff,
          Nat.mod_eq_of_lt (show j.val<10 by omega),Nat.mod_eq_of_lt J]
      rw [eq]
      by_cases z : t=0
      · right; right
        simp [rowSite,z]
      · left; simp [prefixBox,rowSite,Fin.val_ofNat,Nat.mod_eq_of_lt T,Nat.mod_eq_of_lt B]; omega
  rcases bx with ix|rt|zero
  · have nx : ¬IsGridBoundary x := by
      unfold prefixBox at ix; change ¬(_=0 ∨ _+1=Size u ∨ _=0 ∨ _+1=Size u)
      dsimp [Size,high] at *; omega
    obtain ⟨y,via,ex⟩ := physical_frontier_escape F C acy score canon l (t+1) lo hi mark.1 ix nx
    have v' := via.mono (show prefixGraph F l (t+1)≤H from le_sup_left)
    have iy : prefixBox l (t+1) y := by
      obtain ⟨w⟩ := via.symm
      cases w with | nil => exact ix | cons e _ => exact Classical.not_not.mp e.2.1
    rcases ex with (bot|le|ri)|pin
    · right
      let i : Fin 9 := ⟨y.2.val-l,by unfold prefixBox at iy; omega⟩
      refine ⟨⟨i.val,i.isLt.trans (by decide)⟩,?_⟩
      have id : rowPort u l t (retained ⟨i.val,i.isLt.trans (by decide)⟩)=y := by
        have Y := y.2.isLt; have R := y.1.isLt
        have Z : l+i.val=y.2.val := by dsimp [i]; unfold prefixBox at iy; omega
        simp [rowPort,retained,rowSite,i.isLt,show ¬10+i.val<10 by omega,
          Fin.ofNat_eq_cast,Fin.cast_val_eq_self,←bot,Z,Prod.ext_iff,Fin.ext_iff,Nat.mod_eq_of_lt Y,
          Nat.mod_eq_of_lt R,Fin.val_ofNat]
      rw [id]; exact v'
    · exact .inl ⟨y,v',.inr ⟨iy.1,.inl le⟩⟩
    · exact .inl ⟨y,v',.inr ⟨iy.1,.inr ri⟩⟩
    · have ne : y≠nw u := by intro e; rw [e] at iy; simp [prefixBox,nw] at iy
      have edge : H.Adj y (nw u) := built_adj.mpr (.inr (.inr ⟨rfl,pin,iy,ne⟩))
      exact .inl ⟨_,v'.trans edge.reachable,.inl rfl⟩
  · exact .inl ⟨x,.rfl,.inl rt⟩
  · exact (mark.2.1.ne' zero).elim

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
