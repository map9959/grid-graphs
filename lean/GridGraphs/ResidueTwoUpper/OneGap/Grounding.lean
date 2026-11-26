import GridGraphs.ResidueTwoUpper.ExceptionalGapReduction
import GridGraphs.Accounting.BoundaryFive.Rootless.PeelingGraphs

/-! The real perimeter is a legal common terminal for the one-gap strip
calculations: two distinct attachments of a crop component are impossible.
The proof is independent of the charged occurrence. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open SimpleGraph Finset ResidueZero BoundarySix.Connected

theorem perimeter_grounded {n : Nat} (hn : 3≤n) (F : Finset (GridVertex n n))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1) :
    ((Bonds F).induce IsGridBoundary).Preconnected := by
  classical
  let G := perimeterGraph n
  let H := forcedEdgeGraph G (↑(perimeterSelected F) : Set _)
  have eq : H=(Bonds F).induce IsGridBoundary := by
    ext a b
    change ((gridGraph n n).Adj a.1 b.1 ∧ (a∈perimeterSelected F ∨ b∈perimeterSelected F)) ↔
      ((gridGraph n n).Adj a.1 b.1 ∧ (a.1∈F ∨ b.1∈F))
    simp
  have hac : H.IsAcyclic := eq ▸ acy.induce IsGridBoundary
  have led := hac.card_edgeFinset_add_card_connectedComponent
  have deg := G.sum_degrees_eq_twice_card_edges
  have e (v : PerimeterVertex n) : G.degree v=2 := perimeter_degree hn v
  simp only [e,sum_const,card_univ,nsmul_eq_mul] at deg
  change Fintype.card (PerimeterVertex n)*2=2*G.edgeFinset.card at deg
  change H.edgeFinset.card+Fintype.card H.ConnectedComponent=Fintype.card (PerimeterVertex n) at led
  have holes := card_sdiff_add_card_eq_card
    (edgeFinset_mono (forcedEdgeGraph_le G (↑(perimeterSelected F) : Set _)))
  change (perimeterHoles F).card+H.edgeFinset.card=G.edgeFinset.card at holes
  have hs : Subsingleton H.ConnectedComponent := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  rw [←eq]
  intro a b
  exact ConnectedComponent.exact (hs.elim (H.connectedComponentMk a) (H.connectedComponentMk b))

theorem unique_attachment {n : Nat} (hn : 3≤n) (F : Finset (GridVertex n n))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (v w : {v : GridVertex n n // ¬ IsGridBoundary v})
    (a b : PerimeterVertex n)
    (crop : ((Bonds F).induce {v | ¬ IsGridBoundary v}).Reachable v w)
    (ea : (Bonds F).Adj v.1 a.1) (eb : (Bonds F).Adj w.1 b.1) :
    v=w ∧ a=b := by
  obtain ⟨hv,ha⟩ := BoundaryFive.Rootless.forest_cross_edge_unique (Bonds F) acy
    {v | ¬IsGridBoundary v} {v | IsGridBoundary v}
    (Set.disjoint_left.mpr fun _ hi hb => hi hb) v w a b crop (perimeter_grounded hn F acy one b a) ea eb
  exact ⟨Subtype.ext hv,Subtype.ext ha⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
