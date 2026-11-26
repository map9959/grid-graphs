import GridGraphs.NoPitch.TailRows.OverlapCensus
import GridGraphs.Tests.FaceCoverage19

namespace GridGraphs.NoPitch.TailRows.FacePatch
open PitchCut Keys Wired TailCoverage Finset
variable {k b : Nat}

def childAx (i : Fin k) (d : Fin 2) : Fin (N k-2) := ⟨3*i.val+d.val,by
  have := i.isLt; have := d.isLt; unfold N; omega⟩
def child (p : FacePos k) (d : Corner) : PatchPos k := (childAx p.1 d.1,childAx p.2 d.2)

theorem slice_eq (F : Finset (Site k)) (p : FacePos k) (d : Corner) :
    FaceRows.slice (faceMask F p) d=patchMask F (child p d) := by
  funext q
  have ax (i : Fin k) (a : Fin 2) (b : Fin 3) :
      coord i (Fin.ofNat 4 (a.val+b.val))=Fin.ofNat (N k) ((childAx i a).val+b.val) := by
    apply Fin.ext; have := i.isLt; have := a.isLt; have := b.isLt
    simp (disch := omega) only [coord,N,Fin.val_ofNat,childAx,Nat.mod_eq_of_lt]; omega
  simp only [FaceRows.slice,faceMask,ax,child,patchMask]; rfl

def missing (p : PatchPos k) := p.1.val%3==2 || p.2.val%3==2

theorem child_inj : Function.Injective (fun z : FacePos k × Corner => child z.1 z.2) := by
  intro ⟨⟨a,b⟩,r,c⟩ ⟨⟨u,v⟩,i,j⟩ e
  have h := congrArg (fun p : PatchPos k => p.1.val) e
  have g := congrArg (fun p : PatchPos k => p.2.val) e
  dsimp [child,childAx] at h g
  simp only [Prod.mk.injEq,Fin.ext_iff]
  have := r.isLt; have := c.isLt; have := i.isLt; have := j.isLt; omega

theorem child_or_missing (p : PatchPos k) : missing p ∨ ∃ t : FacePos k × Corner, child t.1 t.2=p := by
  by_cases m : missing p; exact Or.inl m
  right; simp [missing] at m
  have r := p.1.isLt; have c := p.2.isLt; unfold N at r c
  exact ⟨((⟨p.1.val/3,by omega⟩,⟨p.2.val/3,by omega⟩),
    ⟨p.1.val%3,by omega⟩,⟨p.2.val%3,by omega⟩),by ext <;> dsimp [child,childAx] <;> omega⟩

/-- The face alphabet sees only first, interior and last on each axis. -/
def band (n z : Nat) : Fin 3 := if z=0 then 0 else if z+1=n then 2 else 1
def faceBand (p : FacePos k) : FacePos 3 := (band k p.1,band k p.2)

def baseAx (b : Nat) (z : Fin 3) := if z=0 then 0 else if z=2 then b-1 else 1
def patchAx (b : Nat) (z : Fin 3) (d : Nat) := 3*baseAx b z+d

def patchBandAx (n z : Nat) := band ((n+1)/3) (z/3)
def patchBand (p : PatchPos k) : FacePos 3 := (patchBandAx (N k-2) p.1,patchBandAx (N k-2) p.2)

theorem child_band (p : FacePos k) (d : Corner) : patchBand (child p d)=faceBand p := by
  have := p.1.isLt; have := d.1.isLt; have := d.2.isLt
  dsimp [patchBand,patchBandAx,child,childAx,faceBand,N]; congr 1 <;> congr 1 <;> omega

theorem face_key (hk : 3≤k) (p : FacePos k) (v : Vector Nat 8) : keyAt p v=keyAt (faceBand p) v := by
  have ax (i : Fin k) : axis (N k-3) 2 (3*i.val)=axis (N 3-3) 2 (3*(band k i).val) ∧
      axis (N k-3) 2 (N k-3-1-3*i.val)=axis (N 3-3) 2 (N 3-3-1-3*(band k i).val) := by
    have := i.isLt; unfold band; split_ifs <;> norm_num [axis,N] <;> (try split_ifs) <;> omega
  unfold keyAt; apply congrArg (fun x => 8*x+2); apply congrArg minimum; funext g
  have r := p.1.isLt; have c := p.2.isLt
  have rev (z : Fin k) : N k-3-1-(N k-3-1-3*z.val)=3*z.val := by have := z.isLt; unfold N; omega
  have rev' (z : Fin 3) : N 3-3-1-(N 3-3-1-3*z.val)=3*z.val := by have := z.isLt; unfold N; omega
  fin_cases g <;> simp [transform,faceBand,rev,rev',(ax _).1,(ax _).2]

/-- An eight-view fine patch representative also preserves the physical
child offset, the face band and the omitted seam. -/
theorem patch_class {p : PatchPos k} {q : PatchPos b} (hk : 19≤k) (hb : 19≤b)
    (e : ∀ g, patchFine p g=patchFine q g) : patchBand p=patchBand q ∧
    p.1.val%3=q.1.val%3 ∧ p.2.val%3=q.2.val%3 := by
  have h := e 0; simp [patchFine,transform,fine] at h
  have ax (i : Fin (N k-2)) (j : Fin (N b-2)) (eq : axis (N k-2) 7 i=axis (N b-2) 7 j) :
      patchBandAx (N k-2) i=patchBandAx (N b-2) j ∧ i.val%3=j.val%3 := by
    have := i.isLt; have := j.isLt; unfold axis at eq
    unfold patchBandAx band N at *; split_ifs at eq ⊢ <;> omega
  obtain ⟨r,x⟩ := ax _ _ h.1; obtain ⟨c,y⟩ := ax _ _ h.2.1
  exact ⟨Prod.ext r c,x,y⟩

end GridGraphs.NoPitch.TailRows.FacePatch
