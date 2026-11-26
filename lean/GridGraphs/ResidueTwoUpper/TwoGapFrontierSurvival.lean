import GridGraphs.ResidueTwoUpper.TwoGapFrontierDelta

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph Finset ResidueZero Stencil Catalogue Words
open scoped Sym2

private theorem fold_edges (H : SimpleGraph V) (p : Fin 19 → V) (es : List Pair) {x y} :
    (es.foldl (addEdge p) H).Adj x y ↔ H.Adj x y ∨
    ∃ e∈es, (edge (p e.1) (p e.2)).Adj x y := by
  induction es generalizing H with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons,ih,addEdge,sup_adj,List.mem_cons]
    grind

variable {u : Nat}
theorem built_update (F : Finset (Board u)) (d l t : Nat) (W : StepWindow u l t) :
    (insertions F d l t).foldl (addEdge (rowPort u l t)) (built F d l t) = built F d l (t+1) := by
  ext x y
  rw [fold_edges]
  constructor
  · rintro (e|⟨a,mem,raw⟩)
    · exact built_monotone F e
    · exact (edge_le_iff _).mpr (.inr (insertion_sound F W a mem).1) raw
  · intro e
    by_cases h : (built F d l t).Adj x y
    · exact .inl h
    obtain ⟨a,m,ends⟩ := insertion_complete F W e h
    exact .inr ⟨a,m,(edge_adj ..).mpr ⟨ends.imp_right And.symm,e.ne⟩⟩

def Represents (F : Finset (Board u)) (d l t : Nat) (s : Frontier) : Prop :=
  s.last=previous F l t ∧ Models (built F d l t) (rootPort u l t) (events F l) s.parts s.tags

theorem physical_advance {d l t : Nat} (F : Finset (Board u)) {P} (C : North.Chart F P d)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (canon : packed (signature (by unfold Size; omega) F)=code4 0 0 1 1)
    (W : StepWindow u l t) {s : Frontier} (rep : Represents F d l t s) :
    ∃ s', advance s (wordRow F l (t+1)) (pinMask (u:=u) d l (t+1))=some s' ∧
      Represents F d l (t+1) s' := by
  let big := pinned (crop (Bonds F) IsGridBoundary) (nw u) (pinSet F d)
  have sub (x : Nat) : built F d l x≤big := by
    intro v w edge
    rcases built_adj.mp edge with ⟨a,b,c,_,_⟩|⟨rfl,p,_,n⟩|⟨rfl,p,_,n⟩
    · exact .inl ⟨a,b,c⟩
    · right; simp only [iSup_adj]; exact ⟨w,p,(edge_adj ..).mpr ⟨.inl ⟨rfl,rfl⟩,n⟩⟩
    · right; simp only [iSup_adj]; exact ⟨v,p,(edge_adj ..).mpr ⟨.inr ⟨rfl,rfl⟩,n⟩⟩
  have forest := physical_frontier_forest F C acy score canon (pinSet F d) (by rfl)
  have hl : 0<l ∧ l+8<Size u := by have := W.lo; have := W.hi; dsimp [high,Size] at *; omega
  have ht : t+1<Size u := by have := W.time; dsimp [high,Size] at *; omega
  have inj := row_inj hl ht
  have fresh := fresh_list (T:=big) (H:=built F d l t) (rowPort u l t) (insertions F d l t)
    (endpoints_nodup _ inj ..) (fun e mem =>
      ⟨sub _ (insertion_sound F W e mem).1,(insertion_sound F W e mem).2⟩)
  have old : rowPort u l t ∘ oldSlot=rootPort u l t := by funext i; simp [rowPort,oldSlot,i.isLt]
  have next : rowPort u l t ∘ retained=rootPort u l (t+1) := by
    funext i; fin_cases i <;> rfl
  have m := rep.2; rw [←old] at m
  have up := built_update F d l t W
  have edges : rowEdges s.last (wordRow F l (t+1)) (pinMask (u:=u) d l (t+1))=insertions F d l t := by
    rw [rep.1]; rfl
  obtain ⟨z,h,last,mod⟩ := advance_survives big _ forest (sub t) _ _ s _ _ m inj
    (row_iso F d l t hl.2 ht) (slot_flags F l t hl ht) (edges ▸ fresh)
    (by rw [edges,up]; exact built_escape F C acy score canon W.lo W.hi W.time)
  rw [edges,up,next] at mod
  exact ⟨z,h,by simpa [previous] using last,mod⟩

theorem initial_rep (F : Finset (Board u)) (d l : Nat) (W : StepWindow u l 0) :
    Represents F d l 0 base := by
  have hl : 0<l ∧ l+8<Size u := by have := W.lo; have := W.hi; dsimp [high,Size] at *; omega
  have ht : 0+1<Size u := by unfold Size; omega
  have inj : Function.Injective (rootPort u l 0) := by
    have eq : rowPort u l 0 ∘ oldSlot=rootPort u l 0 := by funext i; simp [rowPort,oldSlot,i.isLt]
    rw [←eq]; exact (row_inj hl ht).comp (fun _ _ h => Fin.ext (congrArg (fun z : Fin 19 => z.val) h))
  have empty : built F d l 0=⊥ := by
    ext x y; rw [built_adj]; change _ ↔ False
    have no (z : Board u) : ¬prefixBox l 0 z := by unfold prefixBox; omega
    simp [no]
  have idP (i : Fin 10) : base.parts[i.val]! = i.val := by fin_cases i <;> rfl
  have tag (i : Fin 10) (j : Fin 2) :
      base.tags[base.parts[i.val]!]!.testBit j = decide (i=9 ∧ j=0) := by
    revert i j; native_decide
  have ev (i : Fin 10) (j : Fin 2) : events F l j (rootPort u l 0 i) ↔ i=9 ∧ j=0 := by
    have row : (rootPort u l 0 i).1.val=0 := by unfold rootPort; split <;> simp [rowSite,nw]
    have rt : rootPort u l 0 i=nw u ↔ i=9 := ⟨fun e => inj (show rootPort u l 0 i=rootPort u l 0 9 from e),
      fun h => h ▸ rfl⟩
    unfold events; split_ifs <;> simp_all
  refine ⟨rfl,?_⟩
  rw [empty]
  refine ⟨rfl,rfl,fun i => by rw [idP]; exact i.isLt,?_,?_⟩
  · intro i j; rw [idP,idP]; simp [inj.eq_iff,Fin.ext_iff]
  · intro i j; rw [tag]; simp [hits,ev]

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
