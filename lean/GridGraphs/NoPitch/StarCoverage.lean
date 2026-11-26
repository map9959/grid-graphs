import GridGraphs.NoPitch.ColumnProjection
import GridGraphs.Accounting.CarrierLayers.ThreeCarrier.CostTwoEdgeGeometry

namespace GridGraphs.NoPitch.Dual
open PitchCut Keys Finset

def sampled {k} (x : Site k) (bits : Fin 4 → Bool) (d : Nat) :=
  if (probe x d).isSome then (bits (Fin.ofNat 4 d)).toNat else 9

def diagonal {k} (a b : Site k) : Bool := decide (
  (a.1.val+1=b.1.val ∨ b.1.val+1=a.1.val) ∧ (a.2.val+1=b.2.val ∨ b.2.val+1=a.2.val))

def allowed {k} (x : Site k) (bits : Fin 4 → Bool) := ∀ d e : Fin 4,
  bits d → bits e → ((probe x d).any fun a => (probe x e).any (diagonal a))=false

instance {k} (x : Site k) (bits : Fin 4 → Bool) : Decidable (allowed x bits) := by
  unfold allowed; infer_instance

/-- Only the occupied centre contributes to the objective. Every outgoing
direction on the board is enumerated, including a root with no parent. -/
def covers (D : Chart) (k : Nat) :=
  let m := index D
  decide (∀ (x : Site k) (bits : Fin 4 → Bool), allowed x bits →
    ∀ o : Option (Fin 4), (∀ d∈o, (probe x d.val).isSome=true) →
    (locate D m (8*starCode (N k) x.1.val x.2.val (sampled x bits) o+1)).isSome=true)

theorem occupied_covered {D : Chart} {k} (coverage : covers D k) (F : Finset (Site k))
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (out : Site k → Option (Fin 4)) (inside : ∀ x d, d∈out x → (probe x d.val).isSome)
    (x : Site k) (hx : x∈F) : (locate D (index D) (star F out x)).isSome := by
  let bits (d : Fin 4) := (probe x d.val).any (fun a => decide (a∈F))
  have good : allowed x bits := by
    intro d e hd he
    cases a : probe x d.val with
    | none => simp
    | some p =>
      cases b : probe x e.val with
      | none => simp
      | some q =>
        simp [bits,a,b] at hd he
        simp [diagonal]
        intro hr; constructor <;> intro hc
        · exact CarrierLayers.ThreeCarrier.diagonal_preserved_false _ acy p q hd he hr (.inl hc)
        · exact CarrierLayers.ThreeCarrier.diagonal_preserved_false _ acy p q hd he hr (.inr hc)
  have eq (d : Nat) (hd : d<4) : sampled x bits d=neighbor F x d := by
    cases h : probe x d <;> simp [sampled,neighbor,bits,Nat.mod_eq_of_lt hd,h]
  have code : starCode (N k) x.1.val x.2.val (sampled x bits) (out x)=
      starCode (N k) x.1.val x.2.val (neighbor F x) (out x) := by
    unfold starCode
    congr 1; funext g
    have dirs (d : Nat) := eq (direction (invers g) d) (by unfold direction; omega)
    simp only [dirs]
  have hit := of_decide_eq_true coverage x bits good (out x) (inside x)
  simpa [Keys.star,hx,code] using hit

theorem decoded_objective {D : Chart} {k} (ok : unitCheck D) (coverage : covers D k)
    (F : Finset (Site k)) (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (out : Site k → Option (Fin 4)) (inside : ∀ x d, d∈out x → (probe x d.val).isSome) :
    score D (counts D (index D) F out)=8*(F.card:Int) := by
  rw [projected_score D _ ok,filter_eq_self.mpr (occupied_covered coverage F acy out inside)]

noncomputable def physicalVector (D : Chart) (F : Finset (Site k))
    (out : Site k → Option (Fin 4)) (j : Fin D.cols.size) :=
  counts D (index D) F out j + scatter D (index D) (patch F) j +
    (if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0)

/-- All five families use the original decoded column order. -/
theorem vector_objective {D : Chart} {k} (ok : unitCheck D) (positive : D.cols.all (fun c => 0<c.units))
    (coverage : covers D k) (F : Finset (Site k))
    (acy : (forcedEdgeGraph (gridGraph (N k) (N k)) (↑F : Set _)).IsAcyclic)
    (out : Site k → Option (Fin 4)) (inside : ∀ x d, d∈out x → (probe x d.val).isSome) :
    score D (physicalVector D F out)=8*(F.card:Int) := by
  have base := decoded_objective ok coverage F acy out inside
  have patch0 := scatter_score D (index D) ok (patch F)
  have tag (p : PatchPos k) : patch F p%8≠1 := by unfold patch patchCode; omega
  simp only [beq_eq_false_iff_ne.mpr (tag _),Bool.and_false,Bool.false_eq_true,if_false,sum_const_zero] at patch0
  unfold physicalVector score
  simp only [mul_add,sum_add_distrib]
  change score D (counts D (index D) F out)+score D (scatter D (index D) (patch F))+_=_
  rw [base,patch0,add_zero]
  apply add_eq_left.mpr
  apply sum_eq_zero; intro j _
  by_cases aux : D.cols[j].key%8=5
  · have h := beq_iff_eq.mp (Array.all_eq_true_iff_forall_mem.mp ok _ (Array.getElem_mem j.isLt))
    have u := Array.all_eq_true_iff_forall_mem.mp positive _ (Array.getElem_mem j.isLt)
    have ne : D.cols[j].key%8≠1 := by omega
    have hz : D.cols[j].objective*(D.cols[j].units:Int)=0 := by
      change _=(if D.cols[j].key%8=1 then 8 else 0) at h
      rwa [if_neg ne] at h
    have pos : 0<D.cols[j].units := of_decide_eq_true u
    rw [(mul_eq_zero.mp hz).resolve_right (by exact_mod_cast pos.ne')]
    simp
  · rw [if_neg aux,mul_zero]

end GridGraphs.NoPitch.Dual
