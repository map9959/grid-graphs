import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripPhysicalProgram

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph
namespace GridScan

def lattice {n : Nat} (a b : Nat) (i j : Fin n) : Prop :=
  (a+1=b ∨ b+1=a) ∧ i=j ∨ a=b ∧ (i.val+1=j.val ∨ j.val+1=i.val)

theorem lattice_metric {n : Nat} (a b : Nat) (i j : Fin n) :
    lattice a b i j ↔ |(a:Int)-b|+|(i.val:Int)-j.val|=1 := by
  simp only [lattice,Fin.ext_iff,abs_eq_max_neg]
  omega

theorem graph_adj_sites {n : Nat} (p : Row.Program n) (used a b : Nat) (i j : Fin n) :
    (graph p used).Adj (site a i) (site b j) ↔
      0<a ∧ a≤used ∧ 0<b ∧ b≤used ∧ lattice a b i j ∧
        (p.mark (a-1) i=true ∨ p.mark (b-1) j=true) := by
  rw [←mem_edgeSet,graph_edges]
  constructor
  · rintro ⟨t,lt,k,ck,eq⟩
    cases k with
    | vertical z =>
      cases t with
      | zero => simp [choices,Row.Program.previous] at ck
      | succ t =>
        have bits : p.mark t z=true ∨ p.mark (t+1) z=true := by simpa [choices,Row.Program.previous] using ck
        rcases (Sym2.eq_iff.mp eq) with ⟨e,f⟩|⟨e,f⟩ <;>
          simp only [site,Option.some.injEq,Prod.mk.injEq] at e f
        · obtain ⟨rfl,rfl⟩ := e
          obtain ⟨rfl,rfl⟩ := f
          simp only [lattice,Nat.add_sub_cancel]
          exact ⟨by omega,by omega,by omega,by omega,.inl ⟨.inl trivial,trivial⟩,bits⟩
        · obtain ⟨rfl,rfl⟩ := e
          obtain ⟨rfl,rfl⟩ := f
          simp only [lattice,Nat.add_sub_cancel]
          exact ⟨by omega,by omega,by omega,by omega,.inl ⟨.inr trivial,trivial⟩,bits.symm⟩
    | horizontal z =>
      have selected : 0<z.val ∧ (p.mark t (left z)=true ∨ p.mark t z=true) := by
        simpa [choices] using ck
      have near : (left z).val+1=z.val := by
        have := selected.1
        simp [left]; omega
      rcases (Sym2.eq_iff.mp eq) with ⟨e,f⟩|⟨e,f⟩ <;>
        simp only [site,Option.some.injEq,Prod.mk.injEq] at e f
      · obtain ⟨rfl,rfl⟩ := e
        obtain ⟨rfl,rfl⟩ := f
        exact ⟨by omega,by omega,by omega,by omega,.inr ⟨rfl,.inl near⟩,selected.2⟩
      · obtain ⟨rfl,rfl⟩ := e
        obtain ⟨rfl,rfl⟩ := f
        exact ⟨by omega,by omega,by omega,by omega,.inr ⟨rfl,.inr near⟩,selected.2.symm⟩
    | wire z =>
      have eq' := Sym2.eq_iff.mp eq
      simp [site] at eq'
  · rintro ⟨al,ah,bl,bh,near,marks⟩
    rcases near with ⟨e,rfl⟩|⟨rfl,e⟩
    · rcases e with rfl|rfl
      · obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
        exact ⟨t+1,by omega,.vertical i,by simpa [choices,Row.Program.previous] using marks,rfl⟩
      · obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b≠0)
        exact ⟨t+1,by omega,.vertical i,by simpa [choices,Row.Program.previous,or_comm] using marks,Sym2.eq_swap⟩
    · obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
      rcases e with e|e
      · have ij : left j=i := by apply Fin.ext; simp [left]; omega
        exact ⟨t,by omega,.horizontal j,by simpa [choices,ij,show 0 < j.val by omega] using marks,
          by simp [namedEdge,ij]⟩
      · have ji : left i=j := by apply Fin.ext; simp [left]; omega
        exact ⟨t,by omega,.horizontal i,by simpa [choices,ji,show 0 < i.val by omega,or_comm] using marks,
          by simp [namedEdge,ji,Sym2.eq_swap]⟩

theorem graph_adj_root {n : Nat} (p : Row.Program n) (used a : Nat) (i : Fin n) :
    (graph p used).Adj (site a i) none ↔
      0<a ∧ a≤used ∧ p.mark (a-1) i=true ∧ p.tooth (a-1) i=true := by
  rw [←mem_edgeSet,graph_edges]
  constructor
  · rintro ⟨j,jl,k,ck,eq⟩
    cases k with
    | horizontal => simp [namedEdge,site] at eq
    | vertical => simp [namedEdge,site] at eq
    | wire z =>
      simp only [namedEdge,Sym2.eq_iff,site,Option.some.injEq,Prod.mk.injEq,Option.some_ne_none,
        false_and,or_false,and_true] at eq
      obtain ⟨rfl,rfl⟩ := eq
      exact ⟨by omega,by omega,by simpa [choices] using ck⟩
  · rintro ⟨lo,hi,hm,ht⟩
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
    exact ⟨j,by omega,.wire i,by simpa [choices] using And.intro hm ht,rfl⟩

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
