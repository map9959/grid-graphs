import GridGraphs.ResidueTwoUpper.TwoGapFreeOwners

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
open SimpleGraph Finset ResidueZero

private def integral {V : Type*} {G : SimpleGraph V} (w : V → V → Bool) {x y} :
    G.Walk x y → Bool
  | .nil => false
  | @Walk.cons _ _ a b _ _ t => xor (w a b) (integral w t)

private theorem integral_concat {V : Type*} {G : SimpleGraph V} (w : V → V → Bool)
    {a b c} (p : G.Walk a b) (e : G.Adj b c) :
    integral w (p.concat e)=xor (integral w p) (w b c) := by
  induction p with
  | nil => simp [Walk.concat,integral]
  | @cons a b z h p ih => simpa [Walk.concat,integral,Bool.xor_assoc] using congrArg (xor (w a b)) (ih e)

private theorem potential {V : Type*} {G : SimpleGraph V} (tree : G.IsTree) (r : V)
    (w : V → V → Bool) (sym : ∀ x y, w x y=w y x) :
    ∃ s : V → Bool, ∀ x y, G.Adj x y → s y=xor (s x) (w x y) := by
  classical
  let p (x : V) := (tree.connected.preconnected r x).exists_isPath.choose
  have hp (x) : (p x).IsPath := (tree.connected.preconnected r x).exists_isPath.choose_spec
  refine ⟨fun x => integral w (p x),?_⟩
  intro x y e
  change integral w (p y)=xor (integral w (p x)) (w x y)
  by_cases h : x∈(p y).support
  · exact (congrArg (integral w) (tree.isAcyclic.path_concat (hp x) (hp y) e h)).trans (integral_concat ..)
  · have hy := tree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath (hp x) (hp y) e h
    have eq := (congrArg (integral w) (tree.isAcyclic.path_concat (hp y) (hp x) e.symm hy)).trans (integral_concat w (p y) e.symm)
    rw [eq,sym y x]; cases w x y <;> cases integral w (p y) <;> rfl

def wrap (d e : Nat) := (d==0 && e==3) || (d==3 && e==0)

/-- Construct a simultaneous lift of the compass turns to two sheets.
Restricting this very lift to any halo gives the local turn literals. -/
theorem turn_sheet {n} (hn : 1≤n) (F : Finset (GridVertex n n)) (acy : (Bonds F).IsAcyclic)
    (P : GridVertex n n → GridVertex n n) (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (arr : ∀ x y, (Bonds F).Adj x y → (P x=y ↔ P y≠x)) :
    ∃ sheet : GridVertex n n → Bool, ∀ x y z, P x=y → x≠y → P y=z → y≠z →
      sheet y=xor (sheet x) (wrap (outDir x y) (outDir y z)) := by
  classical
  obtain ⟨T,sub,_,tree⟩ := (gridGraph_connected hn hn).exists_isTree_le_of_le_of_isAcyclic
    (show Bonds F≤gridGraph n n from fun _ _ h => h.1) acy
  let wt (x y : GridVertex n n) := (decide (P x=y) && wrap (outDir x y) (outDir y (P y))) ||
    (decide (P y=x) && wrap (outDir y x) (outDir x (P x)))
  obtain ⟨s,hs⟩ := potential tree (⟨0,by omega⟩,⟨0,by omega⟩) wt (fun _ _ => Bool.or_comm ..)
  refine ⟨s,?_⟩
  intro x y z xy ne yz _
  have edge : (Bonds F).Adj x y := xy ▸ step x (by simpa [xy] using ne.symm)
  have back := (arr _ _ edge).mp xy
  have h := hs x y (sub edge)
  simpa [wt,xy,show z≠x from yz ▸ back,yz] using h

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Catalogue
