import GridGraphs.NoPitch.Budget.RemainingRows
import GridGraphs.NoPitch.PhysicalWiring

namespace GridGraphs.NoPitch.LocalBoard19
open Budget PitchCut Keys GridGraphs.NoPitch.Dual Finset Wired
abbrev P := PatchPos 6
abbrev X := Site 6
abbrev Q := Fin 3 × Fin 3

def quad (v : V) : Q := (Fin.ofNat 3 (cell v).1.val,Fin.ofNat 3 (cell v).2.val)
def inside (v : V) := (cell v).1.val<3 && (cell v).2.val<3
def edges := es.filter fun e => inside e.1 && inside e.2
def legal (a : Nine) := fresh initial (edges.filter fun e => a (quad e.1) || a (quad e.2))
def site (p : P) (q : Q) : X :=
  (Fin.ofNat 19 (p.1.val+q.1.val),Fin.ofNat 19 (p.2.val+q.2.val))
def embed (p : P) (v : V) : X :=
  (Fin.ofNat 19 (p.1.val+(cell v).1.val),Fin.ofNat 19 (p.2.val+(cell v).2.val))

theorem patch_legal (F : Finset X) (acy : (Budget.G F).IsAcyclic) (p : P) : legal (patchMask F p) := by
  have inj : ∀ p : P, Function.Injective (embed p) := by native_decide
  have geom : ∀ (p : P) (e : E), e∈edges → e.1<e.2 ∧ (gridGraph 19 19).Adj (embed p e.1) (embed p e.2) ∧
      embed p e.1=site p (quad e.1) ∧ embed p e.2=site p (quad e.2) := by native_decide
  have nd : edges.Nodup := by decide +kernel
  apply fresh_of_forest _ (inj p) (Budget.G F) acy _ (nd.filter _) _ ⊥ bot_le
  · intro x y eq
    have e : x=y := by simpa [initial] using eq
    rw [e]
  · intro e m
    obtain ⟨m,h⟩ := List.mem_filter.mp m
    obtain ⟨ord,adj,a,b⟩ := geom p e m
    refine ⟨ord,⟨adj,?_⟩,by simp⟩
    rw [a,b]
    simpa [patchMask,site] using h

def localStar (x : X) (f : Bool) (bits : Fin 4 → Bool) (o : Option (Fin 4)) :=
  8*starCode 19 x.1.val x.2.val (sampled x bits) o+f.toNat
def permissible (x : X) (bits : Fin 4 → Bool) (f : Bool) (o : Option (Fin 4)) :=
  allowed x bits ∧ ∀ d∈o, (probe x d.val).isSome ∧ (f || bits d)
instance (x : X) (bits f o) : Decidable (permissible x bits f o) := by unfold permissible; infer_instance

theorem physical_perm (F : Finset X) (acy : (Budget.G F).IsAcyclic) (x : X) :
    permissible x (bitsAt F x) (decide (x∈F)) (out F x) := by
  refine ⟨bits_allowed F acy x,fun d hd => ⟨out_inside F x d hd,?_⟩⟩
  have ne : parent F x≠x := fun h => by rw [(out_none F x).mpr h] at hd; cases hd
  have e := (CapBill.parent_step _ (sectionRoot F) (mt (CapBill.parent_fix _ _ x).mpr ne)).1.2
  change x∈F ∨ parent F x∈F at e
  simpa [bitsAt,out_points F x d hd] using e

theorem star_agrees (F : Finset X) (o : X → Option (Fin 4)) (x : X) :
    localStar x (decide (x∈F)) (bitsAt F x) (o x)=Keys.star F o x := by
  have eq : starCode 19 x.1.val x.2.val (sampled x (bitsAt F x)) (o x)=
      starCode 19 x.1.val x.2.val (neighbor F x) (o x) := by
    unfold starCode; apply congrArg minimum; funext g
    have h (d : Nat) := sampled_bits F x (⟨direction (invers g) d,by unfold direction; omega⟩ : Fin 4)
    simp only [h]
  unfold localStar Keys.star; rw [eq]

def supported (D : Chart) (sel : Nat → Bool) := D.cols.all fun c =>
  c.key%8<2 || c.key%8==4 || c.terms.all (fun p => !sel p.1)

theorem star_patch_lhs {D : Chart} {sel : Nat → Bool} (ok : supported D sel)
    (F : Finset X) (o : X → Option (Fin 4)) (i : Fin D.rows.size) (hi : sel i) :
    lhs D (physicalVector D F o) i =
    (∑ x, lookupPrice D i (index D) (Keys.star F o x))+
      ∑ p, lookupPrice D i (index D) (patch F p) := by
  have kill {j : Fin D.cols.size} (n : 2≤D.cols[j].key%8) (p : D.cols[j].key%8≠4) :
      coeff i D.cols[j].terms=0 := by
    have z := Array.all_eq_true_iff_forall_mem.mp ok _ (Array.getElem_mem j.isLt)
    change (_ || _ || D.cols[j].terms.all _)=true at z
    simp only [Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true,Bool.not_eq_true'] at z
    have absent := z.resolve_left (not_or.mpr ⟨not_lt.mpr n,p⟩)
    unfold coeff; apply List.sum_eq_zero; intro t ht
    obtain ⟨a,m,rfl⟩ := List.mem_map.mp ht
    have ne : a.1≠i.val := fun e => by have := absent a m; rw [e,hi] at this; contradiction
    simp [ne]
  have zero (v : Nat) (n : 2≤v%8) (p : v%8≠4) : lookupPrice D i (index D) v=0 := by
    unfold lookupPrice
    cases e : locate D (index D) v with
    | none => rfl
    | some j =>
      change coeff i D.cols[j].terms*_=0
      rw [kill (j:=j) ((locate_key e).symm ▸ n) ((locate_key e).symm ▸ p),zero_mul]
  have faces (p : FacePos 6) : lookupPrice D i (index D) (face F p)=0 := by
    apply zero <;> unfold face faceCode keyAt <;> omega
  have lines (p : Fin 8 × J 6 × J 6) : lookupPrice D i (index D) (line F p.1 p.2.1 p.2.2)=0 := by
    apply zero <;> unfold line <;> dsimp only <;> omega
  have add (u v : Fin D.cols.size → Int) : lhs D (fun j => u j+v j) i=lhs D u i+lhs D v i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _; dsimp only; split <;> rename_i h
    · rw [kill (j:=j) (by omega) (by omega),zero_mul]
    · simp
  unfold physicalVector counts
  rw [add,add,add,add,aux]
  simp only [scatter_price,faces,lines,sum_const_zero,add_zero]

end GridGraphs.NoPitch.LocalBoard19
