import GridGraphs.Geometry.PitchTracePrice
import GridGraphs.Results.ExactSquareFormula

namespace GridGraphs.PitchCut
open SimpleGraph Finset GridGraphs.Slit.Replay

abbrev N (k : Nat) := 3*k+1
abbrev Site (k : Nat) := GridVertex (N k) (N k)
def teeth (k : Nat) : Fin (k+1) ↪ Fin (N k) where
  toFun i := ⟨3*i.val,by dsimp [N]; omega⟩
  inj' := by intro i j e; apply Fin.ext; have := congrArg Fin.val e; dsimp at this; omega

def rowTeeth (k : Nat) (v : Fin (N k)) :=
  univ.image (fun i : Fin (k+1) => (v,teeth k i))

def confined {V : Type*} (G : SimpleGraph V) (p : V → Prop) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ p x ∧ p y
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

def aboveCap {k : Nat} (F : Finset (Site k)) (v : Fin (N k)) :=
  confined (forcedEdgeGraph (gridGraph (N k) (N k)) ↑F) (fun x => x.1.val<v.val)
def belowCap {k : Nat} (F : Finset (Site k)) (v : Fin (N k)) :=
  confined (forcedEdgeGraph (gridGraph (N k) (N k)) ↑F) (fun x => v.val≤x.1.val)
def aboveBonus {k : Nat} (F : Finset (Site k)) (v : Fin (N k)) : Int :=
  ((F.filter fun x => x.1.val<v.val).card : Int)-v.val*((k:ℤ)+1)
def belowBonus {k : Nat} (F : Finset (Site k)) (v : Fin (N k)) : Int :=
  ((F.filter fun x => v.val<x.1.val).card : Int)-(N k-1-v.val : Nat)*((k:ℤ)+1)

def Pitch {k : Nat} (F : Finset (Site k)) (v : Fin (N k)) :=
  (F.filter fun x => x.1=v) = rowTeeth k v

theorem pitch_score {k : Nat} (F : Finset (Site k)) (v : Fin (N k)) (pitch : Pitch F v) :
    (F.card : Int) = (N k : Int)*((k:ℤ)+1)+aboveBonus F v+belowBonus F v := by
  have row : (rowTeeth k v).card=k+1 := by
    unfold rowTeeth
    rw [card_image_of_injective _ (by intro i j h; exact (teeth k).injective (Prod.mk.inj h).2)]
    simp
  have h₁ := card_filter_add_card_filter_not (s := F) (p := fun x => x.1.val<v.val)
  have h₂ := card_filter_add_card_filter_not
    (s := F.filter fun x => ¬x.1.val<v.val) (p := fun x => x.1=v)
  have e₁ : ((F.filter fun x => ¬x.1.val<v.val).filter fun x => x.1=v) =
      F.filter fun x => x.1=v := by ext x; simp; grind
  have e₂ : ((F.filter fun x => ¬x.1.val<v.val).filter fun x => ¬x.1=v) =
      F.filter fun x => v.val<x.1.val := by
    ext x; simp only [mem_filter, Fin.ext_iff]; grind
  rw [e₁,e₂,pitch,row] at h₂
  have counts : (F.card : Int) = ((F.filter fun x => x.1.val<v.val).card : Int)+
    ((F.filter fun x => v.val<x.1.val).card : Int)+(k+1) := by omega
  have height : ((N k-1-v.val : Nat) : Int) = (N k : Int)-1-v.val := by
    have := v.isLt; omega
  rw [counts,aboveBonus,belowBonus,height]; ring

/-- The physical inequality uses the graphs forced by these marked sites,
not an assumption on an abstract interface partition. -/
theorem marked_rank {k : Nat} (F : Finset (Site k)) {T : SimpleGraph (Site k)}
    (tree : IsSpanningSubtree (gridGraph (N k) (N k)) T)
    (forced : forcedEdgeGraph (gridGraph (N k) (N k)) ↑F ≤ T)
    (u v : Fin (N k)) (next : u.val+1=v.val) (pitch : Pitch F v) :
    rank (aboveCap F v) (fun i => (u,teeth k i)) +
      rank (belowCap F v) (fun i => (v,teeth k i)) ≤ k := by
  apply grid_shared_rank tree u v next (teeth k)
  · intro i
    apply preservesIncidentEdges_of_forcedEdgeGraph_le forced
    have h : (v,teeth k i) ∈ rowTeeth k v := mem_image_of_mem _ (mem_univ i)
    rw [←pitch] at h
    exact (mem_filter.mp h).1
  · intro _ _ e; exact forced e.1
  · intro _ _ e; exact forced e.1
  · intro x y e; have := e.2.2; omega
  · intro x y e; exact e.2.1

/-- Remaining bridge stated with concrete, computable cap quantities. In
particular the score decomposition and shared rank are *not* premises. -/
theorem marked_upper_of_traces (ok : replay requests) {k : Nat} (hk : 5≤k)
    (F : Finset (Site k)) {T : SimpleGraph (Site k)}
    (tree : IsSpanningSubtree (gridGraph (N k) (N k)) T)
    (forced : forcedEdgeGraph (gridGraph (N k) (N k)) ↑F ≤ T)
    (u v : Fin (N k)) (next : u.val+1=v.val) (pitch : Pitch F v)
    (L : CapTrace k (rank (aboveCap F v) fun i => (u,teeth k i)) (aboveBonus F v))
    (R : CapTrace k (rank (belowCap F v) fun i => (v,teeth k i)) (belowBonus F v)) :
    F.card ≤ squareScore (N k) := by
  have sh := marked_rank F tree forced u v next pitch
  obtain ⟨lp,lc⟩ := trace_tariff ok hk L
  obtain ⟨rp,rc⟩ := trace_tariff ok hk R
  have s := PitchSkeletonPrice.uniformPitchBonus k _ _ _ _ (by omega)
    (Int.natCast_nonneg _) (Int.natCast_nonneg _) (by exact_mod_cast sh)
    (by intro e; exact lp (by exact_mod_cast e)) (by intro e; exact lc (by exact_mod_cast e))
    (by intro e; exact rp (by exact_mod_cast e)) (by intro e; exact rc (by exact_mod_cast e))
  have ledger := pitch_score F v pitch
  unfold N at ledger ⊢
  rw [squareScore_three_mul_add_one k (by omega)]
  zify [show 13≤3*k by omega]
  push_cast at ledger ⊢
  linarith only [s,ledger]

end GridGraphs.PitchCut
