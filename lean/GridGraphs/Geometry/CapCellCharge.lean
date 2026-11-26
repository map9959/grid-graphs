import GridGraphs.Geometry.CapGuardScan

namespace GridGraphs.CapSite
open GridGraphs.CapBill Finset

def neighbor (c : Camera) (y x : Int) (i : Fin 4) : Pt :=
  if i=0 then c.atP y (x-1) else if i=1 then c.atP y (x+1)
  else if i=2 then c.atP (y-1) x else c.atP (y+1) x

private theorem neighbor_inj (c : Camera) (y x : Int) :
    Function.Injective (neighbor c y x) := by
  intro i j eq
  fin_cases i <;> fin_cases j <;> simp_all [neighbor,Camera.atP] <;>
    first | omega | split_ifs at eq <;> omega

private theorem neighbors_iff (c : Camera) (y x : Int) (q : Pt) :
    unitEdge q (c.atP y x) ↔ ∃ i : Fin 4, neighbor c y x i=q := by
  rcases q with ⟨a,b⟩
  simp [Fin.exists_fin_succ,neighbor,unitEdge,Camera.atP]
  split_ifs <;> omega

private theorem occurs_iff {r h} (F : Finset (Cell r h)) (v : Cell r h) :
    onBoard F (coord v) ↔ v∈F := by
  constructor
  · rintro ⟨w,hw,e⟩; exact coord_injective e ▸ hw
  · exact (⟨_,·,rfl⟩)

theorem physical_hits {r h} (F : Finset (Cell r h)) (c : Camera) (y x : Int)
    (v : Cell r h) (co : coord v=c.atP y x) :
    touches (atStencil F c y x)=hits (board r h) F v := by
  classical
  let near := F.filter (fun w => (board r h).Adj w v)
  let marked := univ.filter (fun i : Fin 4 => onBoard F (neighbor c y x i))
  have eq : near.image coord = marked.image (neighbor c y x) := by
    ext q
    simp only [mem_image,near,marked,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨w,⟨wm,e⟩,rfl⟩
      have adj : unitEdge (coord w) (coord v) := by
        change (_ ∨ _) at e
        simp only [unitEdge,coord,Fin.ext_iff] at *; omega
      rw [co,neighbors_iff] at adj; obtain ⟨i,hi⟩ := adj
      exact ⟨i,⟨_,wm,hi.symm⟩,hi⟩
    · rintro ⟨i,⟨w,wm,e⟩,rfl⟩
      have adj := (neighbors_iff c y x _).mpr ⟨i,e.symm⟩
      rw [←co] at adj
      refine ⟨w,⟨wm,?_⟩,e⟩
      change _ ∨ _; simp only [unitEdge,coord] at adj; simp only [Fin.ext_iff]; omega
  have cards := congrArg Finset.card eq
  rw [card_image_of_injective _ coord_injective,card_image_of_injective _ (neighbor_inj ..)] at cards
  unfold hits
  change _ = (near.card : Int)
  rw [cards]; dsimp only [marked]; rw [card_filter]
  simp [Fin.sum_univ_four,touches,atStencil,markBit,one,neighbor]

theorem physical_geom {r h} (F : Finset (Cell r h)) (c : Camera) (y x : Int)
    (v : Cell r h) (co : coord v=c.atP y x) :
    geometry (decide (v.2.val%3=1)) (atStencil F c y x) =
      siteBill (board r h) F (outer r h) v := by
  classical
  have mk : markBit F c y x = decide (v∈F) := by
    apply Bool.eq_iff_iff.mpr
    simp [markBit,←co,occurs_iff]
  unfold geometry
  rw [physical_hits _ _ _ _ _ co]
  simp only [atStencil,mk]
  by_cases hf : v ∈ F <;> by_cases center : v.2.val%3=1 <;>
    simp [siteBill,iso,outer,one,hf,center]

private theorem no_send {r h} (F : Finset (Cell r h)) (c : Camera) (y x : Int)
    (v : Cell r h) (co : coord v=c.atP y x) : keeps (board r h) (terminalSet F) F v ↔
    toward F c y x (-1) 0=false ∧ toward F c y x 0 (-1)=false ∧
      toward F c y x 0 1=false ∧ toward F c y x 1 0=false := by
  have eq := sending_iff (F:=F) v
  rw [co] at eq
  constructor
  · intro k
    have none := mt eq.mp (not_not.mpr k)
    have f (a b : Int) : toward F c y x a b=false := by
      apply Bool.eq_false_iff.mpr
      intro out; exact none ⟨_,(toward_iff ..).mp out⟩
    exact ⟨f ..,f ..,f ..,f ..⟩
  · rintro ⟨a,b,d,e⟩; by_contra neg
    have or := four_directions F c (eq.mpr neg)
    simp_all

theorem physical_sink {r h} (F : Finset (Cell r h)) (c : Camera) (y i : Nat) (hi : i<3)
    (v : Cell r h) (co : coord v=c.atP y ((i:ℤ)+1)) :
    (freeSink (stateAt F c y) (rowAt F c y) i) = decide (v∈extraRoots (board r h) (terminalSet F) F) := by
  classical
  have mk : markBit F c y ((i:ℤ)+1)=decide (v∈F) := by
    apply Bool.eq_iff_iff.mpr; simp [markBit,←co,occurs_iff]
  have yy : v.1.val=y := by exact_mod_cast (Prod.mk.inj co).1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,extraRoots,mem_filter,no_send F c y _ v co]
  have ht : v∈terminalSet F ↔ v∈F ∧ y=0 := by change v∈F.filter _ ↔ _; rw [mem_filter,←yy]
  simp [freeSink,state_first,sent_state,old_state,rowAt,maskAt,packed,hi,
    show i+1<5 by omega,usedAt,mk,ht]
  tauto

end GridGraphs.CapSite
