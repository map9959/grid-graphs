import GridGraphs.Geometry.PitchPadRank
import GridGraphs.Results.CombLower

/-! The residue-one upper bound when the physical mark set has a pitch
row. Only the two closed, reproducible table evaluations are separated
out. No cap words, budgets or rank hypotheses are inputs. -/
namespace GridGraphs.PitchCut
open SimpleGraph Finset GridGraphs.CapBill GridGraphs.CapSite GridGraphs.Slit.Replay

private theorem waived_rank {r h} {F : Finset (Cell r h)} (pad : Padded F) :
    (waived (board r h) (terminalSet F) F).card=rank (bonds F) tooth := by
  classical
  let T := terminalSet F
  let e : Fin T.card ≃ ↥T := (finCongr (Fintype.card_coe T).symm).trans (Fintype.equivFin ↥T).symm
  have rankEq := waived_eq_rank (board r h) T F e
  rw [rankEq,rank,rank,Fintype.card_fin,Fintype.card_fin]
  apply congrArg₂ Nat.sub pad.teeth
  have a : univ.image (fun i => ((e i).val))=T := by
    ext v; simp only [mem_image,mem_univ,true_and]; constructor
    · rintro ⟨i,rfl⟩; exact (e i).property
    · intro m; exact ⟨e.symm ⟨v,m⟩,by simp⟩
  have b := terminal_eq pad
  unfold classes
  have eq := congrArg (fun X : Finset _ => X.image (bonds F).connectedComponentMk) (a.trans b)
  simpa [image_image,Function.comp_def] using congrArg card eq

variable {k : Nat} (F : Finset (Site k)) (v : Fin (N k))

private theorem side_count (up : Bool) :
    (mask v up F).card=(F.filter (onSide v up)).card := by
  apply card_bij (fun z _ => project v up z)
  · intro z hz; exact mem_filter.mpr ⟨((mask_mem ..).mp hz).2,project_side ..⟩
  · intro x hx y hy eq
    rw [←recover_inner v up x ((mask_mem ..).mp hx).1,←recover_inner v up y ((mask_mem ..).mp hy).1,eq]
  · intro x hx
    obtain ⟨m,s⟩ := mem_filter.mp hx
    have eq := recover_side v up x s
    exact ⟨embed v up x,(mask_mem ..).mpr ⟨embed_inner ..,by rwa [eq]⟩,eq⟩

def bonus (up : Bool) := if up then aboveBonus F v else belowBonus F v
private theorem bonus_eq (up : Bool) (pitch : Pitch F v) :
    ((mask v up F).card : Int)-((k:ℤ)+1)*((height v up:ℤ)+1)=bonus F v up := by
  rw [side_count]
  let S := F.filter (onSide v up)
  have split := card_filter_add_card_filter_not (s:=S) (p:=fun x => x.1=v)
  have row : S.filter (fun x => x.1=v) = rowTeeth k v := by
    rw [←pitch]; ext x
    simp [S,onSide]; cases up <;> simp_all
  have sz : (rowTeeth k v).card=k+1 := by
    rw [rowTeeth,card_image_of_injective _ (fun _ _ eq => (teeth k).injective (Prod.mk.inj eq).2)]
    simp
  rw [row,sz] at split
  change (S.card : Int)-_=_
  cases up
  · have free : S.filter (fun x => ¬x.1=v)=F.filter (fun x => v.val<x.1.val) := by
      ext x; simp only [S,onSide,mem_filter,Fin.ext_iff,Bool.false_eq_true,if_false]; grind
    rw [free] at split
    simp only [height,bonus,Bool.false_eq_true,if_false,belowBonus]
    rw [←split]; push_cast; ring
  · have free : S.filter (fun x => ¬x.1=v)=F.filter (fun x => x.1.val<v.val) := by
      ext x; simp only [S,onSide,mem_filter,Fin.ext_iff,if_true]; grind
    rw [free] at split
    simp only [height,bonus,if_true,aboveBonus]
    rw [←split]; push_cast; ring

noncomputable def trace_of_pitch (localOK : tablesOK) (hk : 5≤k) (up : Bool)
    (pitch : Pitch F v) (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic) :
    CapTrace k (rank (inclusive F v up) fun i => (v,teeth k i)) (bonus F v up) := by
  have pad := pad_mask v up pitch acy
  have C := paddedCapTrace localOK hk pad
  rw [waived_rank pad,inclusive_rank,bonus_eq F v up pitch] at C
  exact C

/-- At any pitch row with a predecessor, build both witnesses from the
physical forest, then use the shared physical rank in one square. -/
theorem pitch_upper_interior (localOK : tablesOK) (ok : replay requests)
    (hk : 5≤k) {T : SimpleGraph (Site k)} (tree : IsSpanningSubtree (gridGraph (N k) (N k)) T)
    (forced : forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _) ≤ T)
    (u : Fin (N k)) (next : u.val+1=v.val) (pitch : Pitch F v) : F.card ≤ squareScore (N k) := by
  have acy := tree.isAcyclic.anti forced
  have hi := trace_of_pitch F v localOK hk true pitch acy
  rw [upper_rank F v u next pitch acy] at hi
  exact marked_upper_of_traces ok hk F tree forced u v next pitch hi
    (trace_of_pitch F v localOK hk false pitch acy)

/-- Includes row zero, for which there is no upper spoke to delete. -/
theorem pitch_upper (localOK : tablesOK) (ok : replay requests)
    (hk : 5≤k) {T : SimpleGraph (Site k)} (tree : IsSpanningSubtree (gridGraph (N k) (N k)) T)
    (forced : forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _) ≤ T)
    (pitch : Pitch F v) : F.card ≤ squareScore (N k) := by
  by_cases top : v.val=0
  · let q := rank (inclusive F v false) (fun i => (v,teeth k i))
    have R := trace_of_pitch F v localOK hk false pitch (tree.isAcyclic.anti forced)
    change CapTrace k q (belowBonus F v) at R
    have qle : q≤k := by
      have := R.kept; have := R.pos; omega
    obtain ⟨vp,vc⟩ := trace_tariff ok hk R
    have pair := PitchSkeletonPrice.uniformPitchBonus k 0 q 0 (belowBonus F v)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by intro e; exact vp (by omega)) (by intro e; exact vc (by omega))
    have score := pitch_score F v pitch
    have zero : aboveBonus F v=0 := by simp [aboveBonus,top]
    rw [zero] at score
    unfold N at score ⊢; rw [squareScore_three_mul_add_one k (by omega)]
    zify [show 13≤3*k by omega]; push_cast at score ⊢
    linarith only [score,pair]
  · exact pitch_upper_interior F v localOK ok hk tree forced
      ⟨v.val-1,by have := v.isLt; omega⟩ (by dsimp; omega) pitch

def transpose (F : Finset (Site k)) := F.image Prod.swap

theorem acyclic_pitch_upper (localOK : tablesOK) (ok : replay requests)
    (hk : 5≤k) (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (pitch : Pitch F v ∨ Pitch (transpose F) v) : F.card ≤ squareScore (N k) := by
  classical
  let G := gridGraph (N k) (N k)
  have byRow (S : Finset (Site k)) (p : Pitch S v) (a : (forcedEdgeGraph G (↑S : Set _)).IsAcyclic) :
      S.card ≤ squareScore (N k) := by
    obtain ⟨T,sub,le,tree⟩ := (gridGraph_connected (m:=N k) (n:=N k) (by dsimp [N]; omega)
      (by dsimp [N]; omega)).exists_isTree_le_of_le_of_isAcyclic (forcedEdgeGraph_le G _) a
    exact pitch_upper S v localOK ok hk ⟨le,tree⟩ sub p
  rcases pitch with p|p
  · exact byRow F p acy
  · let hom : forcedEdgeGraph G (↑(transpose F) : Set _) →g forcedEdgeGraph G (↑F : Set _) := by
      refine ⟨Prod.swap,?_⟩
      intro x y e
      have mark (z : Site k) (m : z∈transpose F) : z.swap∈F := by
        obtain ⟨w,mem,rfl⟩ := mem_image.mp m
        exact mem
      exact ⟨e.1.elim Or.inr Or.inl,e.2.imp (mark x) (mark y)⟩
    have bound := byRow (transpose F) p (acy.comap hom (fun _ _ eq => Prod.swap_injective eq))
    rwa [transpose,card_image_of_injective _ Prod.swap_injective] at bound

end GridGraphs.PitchCut

namespace GridGraphs.PitchCut

/-- The no-pitch dual need only rule out *maximizing* physical mark sets
above the comb; it need not price arbitrary smaller or fractional sets. -/
theorem exact_of_no_pitch (localOK : CapSite.tablesOK) (ok : Slit.Replay.replay Slit.Replay.requests)
    {k : Nat} (hk : 5≤k)
    (noPitch : ∀ F : Finset (Site k), F ∈ acyclicForcedSets (N k) (N k) →
      F.card=maxPreserved (N k) (N k) →
      (∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) → F.card ≤ squareScore (N k)) :
    maxPreserved (N k) (N k) = squareScore (N k) := by
  classical
  apply Nat.le_antisymm _ (squareScore_lower_residue_one k)
  obtain ⟨F,hF,score⟩ := (squareMaskScore_iff_le (n:=N k) (s:=maxPreserved (N k) (N k))
    (by unfold N; omega)).mpr le_rfl
  rw [←score]
  by_cases p : ∃ v, Pitch F v ∨ Pitch (transpose F) v
  · obtain ⟨v,p⟩ := p
    exact acyclic_pitch_upper F v localOK ok hk (mem_acyclicForcedSets.mp hF) p
  · exact noPitch F hF score (fun v h => p ⟨v,h⟩)

end GridGraphs.PitchCut
