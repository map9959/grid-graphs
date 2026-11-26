import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripTraceClosure

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph

namespace GridScan

/-- Row zero consists of the initial dummy vertices. Real row `j`
has vertex index `j+1`, and `none` is the permanent virtual root. -/
abbrev Vertex (n : Nat) := Option (Nat × Fin n)

def site {n : Nat} (j : Nat) (i : Fin n) : Vertex n := some (j,i)

def frontier (n j : Nat) : Fin (n+1) → Vertex n :=
  Fin.lastCases none (site j)

def slots (n j : Nat) : Fin (n+1+n) → Vertex n :=
  Fin.addCases (frontier n j) (site (j+1))

@[simp] theorem frontier_cast {n j : Nat} (i : Fin n) :
    frontier n j i.castSucc=site j i := Fin.lastCases_castSucc i
@[simp] theorem frontier_root (n j : Nat) :
    frontier n j (Fin.last n)=none := Fin.lastCases_last
@[simp] theorem slots_old {n j : Nat} (i : Fin (n+1)) :
    slots n j (Row.oldSlot i)=frontier n j i := Fin.addCases_left i
@[simp] theorem slots_new {n j : Nat} (i : Fin n) :
    slots n j (Row.newSlot i)=site (j+1) i := Fin.addCases_right i

theorem slots_reuses (n j : Nat) : slots n j ∘ Row.oldSlot=frontier n j := by
  funext i; exact slots_old i

theorem slots_retains (n j : Nat) : slots n j ∘ Row.keep=frontier n (j+1) := by
  funext i
  refine Fin.lastCases ?_ (fun x => ?_) i
  · simp [Row.keep]
  · simp [Row.keep]

theorem slots_injective (n j : Nat) : Function.Injective (slots n j) := by
  intro i k
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) k
  · refine Fin.lastCases ?_ (fun x => ?_) a <;>
      refine Fin.lastCases ?_ (fun y => ?_) b <;> simp [site]
  · refine Fin.lastCases ?_ (fun x => ?_) a <;> simp [site]
  · refine Fin.lastCases ?_ (fun x => ?_) b <;> simp [site]
  · simp [site]

private theorem evenEdge {V : Type} {a b : V} (e : Sym2 V) :
    e∈(SimpleGraph.edge a b).edgeSet ↔ e=s(a,b) ∧ a≠b := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    rw [mem_edgeSet,edge_adj,Sym2.eq_iff]
    constructor
    · rintro ⟨h,ne⟩
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨.inl ⟨rfl,rfl⟩,ne⟩
      · exact ⟨.inr ⟨rfl,rfl⟩,ne.symm⟩
    · rintro ⟨h,ne⟩
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨.inl ⟨rfl,rfl⟩,ne⟩
      · exact ⟨.inr ⟨rfl,rfl⟩,ne.symm⟩

def code {V : Type} {n : Nat} (f : Fin n → V) (e : SlotEdge n) : Sym2 V :=
  s(f e.1, f e.2)

theorem addEdges_edgeSet {V : Type} {n : Nat} (f : Fin n → V) (G : SimpleGraph V)
    (es : List (SlotEdge n)) (offDiag : ∀ e∈es, f e.1≠f e.2) :
    (addEdges f G es).edgeSet = G.edgeSet ∪ {e | e∈es.map (code f)} := by
  induction es generalizing G with
  | nil => ext e; simp [addEdges]
  | cons x xs ih =>
    obtain ⟨a,b⟩ := x
    have ne := offDiag (a,b) (by simp)
    have h := ih (G ⊔ SimpleGraph.edge (f a) (f b)) (fun e he => offDiag e (by simp [he]))
    rw [addEdges,h,edgeSet_sup]
    ext e
    simp only [Set.mem_union,Set.mem_ofPred_eq,List.map_cons,List.mem_cons,evenEdge,code]
    tauto

/-- Checking a generated row is reduced to edge membership,
uniqueness of undirected edge codes, and absence from the old graph. -/
theorem freshSchedule_of_codes {V : Type} {n : Nat} (f : Fin n → V) {W G : SimpleGraph V}
    (es : List (SlotEdge n)) (distinct : (es.map (code f)).Nodup)
    (inW : ∀ e∈es, code f e∈W.edgeSet)
    (new : ∀ e∈es, code f e∉G.edgeSet) :
    FreshSchedule f W G es := by
  induction es generalizing G with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨a,b⟩ := x
    have d := List.nodup_cons.mp distinct
    refine ⟨(mem_edgeSet W).mp (inW (a,b) (by simp)),
      fun h => new (a,b) (by simp) ((mem_edgeSet G).mpr h),?_⟩
    apply ih d.2 (fun e he => inW e (by simp [he]))
    intro e he h
    rw [edgeSet_sup,Set.mem_union,evenEdge] at h
    rcases h with h|⟨h,_⟩
    · exact new e (by simp [he]) h
    · exact d.1 (List.mem_map.mpr ⟨e,he,h⟩)

inductive Kind (n : Nat) where
  | vertical : Fin n → Kind n
  | horizontal : Fin n → Kind n
  | wire : Fin n → Kind n
deriving DecidableEq

def left {n : Nat} (i : Fin n) : Fin n := ⟨i.val-1,by have := i.isLt; omega⟩

def namedEdge {n : Nat} (j : Nat) : Kind n → Sym2 (Vertex n)
  | .vertical i => s(site j i,site (j+1) i)
  | .horizontal i => s(site (j+1) (left i),site (j+1) i)
  | .wire i => s(site (j+1) i,none)

theorem namedEdge_injective {n : Nat} (j : Nat) : Function.Injective (@namedEdge n j) := by
  intro a b h
  cases a <;> cases b <;>
    simp [namedEdge,site,Fin.ext_iff,left] at h ⊢ <;> omega

def choices {n : Nat} (p : Row.Program n) (j : Nat) : Kind n → Bool
  | .vertical i => (p.previous j).any (fun old => old i || p.mark j i)
  | .horizontal i => decide (0 < i.val) && (p.mark j (left i) || p.mark j i)
  | .wire i => p.mark j i && p.tooth j i

private def names (n : Nat) : List (Kind n) :=
  (List.finRange n).flatMap fun i => [.vertical i,.horizontal i,.wire i]

private theorem names_nodup (n : Nat) : (names n).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _
    simp
  · apply (List.nodup_finRange n).imp
    intro a b ne
    apply List.disjoint_left.mpr
    intro x hx hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with rfl|rfl|rfl <;> simp_all

def scheduled {n : Nat} (p : Row.Program n) (j : Nat) : List (SlotEdge (n+1+n)) :=
  Row.edges (p.previous j) (p.mark j) (p.tooth j)

theorem scheduled_codes {n : Nat} (p : Row.Program n) (j : Nat) :
    (scheduled p j).map (code (slots n j)) =
      ((names n).filter (choices p j)).map (namedEdge j) := by
  rw [scheduled,Row.edges,names,List.filter_flatMap,List.map_flatMap,List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  let a := (p.previous j).any (fun old => old i || p.mark j i)
  let c := p.mark j i && p.tooth j i
  let b := p.mark j (left i) || p.mark j i
  have predEq (h : 0 < i.val) :
      (⟨i.val-1,by have := i.isLt; omega⟩ : Fin n)=left i := rfl
  by_cases hi : 0 < i.val <;>
    cases ha : a <;> cases hb : b <;> cases hc : c <;>
    dsimp only [a,b,c] at ha hb hc <;>
    simp only [choices,List.filter_cons,List.filter_nil,hi,if_true,if_false,
      dif_pos,predEq,ha,hb,hc,Bool.false_eq_true,
      decide_true,decide_false,Bool.true_and,Bool.false_and,
      List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,
      namedEdge,code,slots_old,slots_new,frontier_cast,frontier_root] <;> simp

theorem scheduled_nodup {n : Nat} (p : Row.Program n) (j : Nat) :
    ((scheduled p j).map (code (slots n j))).Nodup := by
  rw [scheduled_codes]
  exact ((names_nodup n).filter _).map (namedEdge_injective j)

theorem scheduled_mem {n : Nat} (p : Row.Program n) (j : Nat) (e : Sym2 (Vertex n)) :
    e∈(scheduled p j).map (code (slots n j)) ↔
      ∃ k, choices p j k=true ∧ namedEdge j k=e := by
  rw [scheduled_codes]
  simp only [List.mem_map,List.mem_filter]
  have all (k : Kind n) : k∈names n := by
    cases k <;> rename_i i <;> exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,by simp⟩
  simp only [all,true_and]

def level {n : Nat} : Vertex n → Nat
  | none => 0
  | some (j,_) => j

def grade {n : Nat} : Sym2 (Vertex n) → Nat :=
  Sym2.lift ⟨fun a b => max (level a) (level b),fun _ _ => max_comm _ _⟩

@[simp] theorem grade_mk {n : Nat} (a b : Vertex n) :
    grade s(a,b)=max (level a) (level b) := rfl

theorem namedEdge_grade {n : Nat} (j : Nat) (k : Kind n) :
    grade (namedEdge j k)=j+1 := by
  cases k <;> simp [namedEdge,site,level]

theorem namedEdge_offDiag {n : Nat} (p : Row.Program n) (j : Nat) (k : Kind n)
    (chosen : choices p j k=true) : namedEdge j k∉Sym2.diagSet := by
  cases k with
  | vertical => simp [namedEdge,site,Sym2.mem_diagSet,Sym2.mk_isDiag_iff]
  | wire => simp [namedEdge,site,Sym2.mem_diagSet,Sym2.mk_isDiag_iff]
  | horizontal i =>
    simp only [choices,Bool.and_eq_true,decide_eq_true_eq] at chosen
    simp only [namedEdge,site,Sym2.mem_diagSet,Sym2.mk_isDiag_iff,Option.some.injEq,
      Prod.mk.injEq,true_and,Fin.ext_iff,left]
    omega

/-- The actual processed graph: rows contribute their lattice bonds
and selected wires, each under its own scan index. -/
def graph {n : Nat} (p : Row.Program n) (used : Nat) : SimpleGraph (Vertex n) :=
  fromEdgeSet {e | ∃ j<used, ∃ k, choices p j k=true ∧ namedEdge j k=e}

theorem graph_edges {n : Nat} (p : Row.Program n) (used : Nat) (e : Sym2 (Vertex n)) :
    e∈(graph p used).edgeSet ↔ ∃ j<used, ∃ k, choices p j k=true ∧ namedEdge j k=e := by
  rw [graph,edgeSet_fromEdgeSet]
  constructor
  · exact fun h => h.1
  · rintro ⟨j,hj,k,ck,rfl⟩
    exact ⟨⟨j,hj,k,ck,rfl⟩,namedEdge_offDiag p j k ck⟩

theorem graph_mono {n : Nat} (p : Row.Program n) {j k : Nat} (le : j≤k) :
    graph p j ≤ graph p k := by
  apply edgeSet_subset_edgeSet.mp
  intro e mem
  obtain ⟨t,bt,kind,ch,eq⟩ := (graph_edges p j e).mp mem
  exact (graph_edges p k e).mpr ⟨t,lt_of_lt_of_le bt le,kind,ch,eq⟩

theorem graph_zero {n : Nat} (p : Row.Program n) : graph p 0=⊥ := by
  apply edgeSet_injective
  ext e
  simp [graph_edges]

theorem graph_new_isolated {n : Nat} (p : Row.Program n) (j : Nat) (i : Fin n) :
    (graph p j).IsIsolated (site (j+1) i) := by
  intro b adj
  obtain ⟨t,lt,k,_,e⟩ := (graph_edges p j _).mp ((mem_edgeSet _).mpr adj)
  have rank := namedEdge_grade t k
  rw [e,grade_mk] at rank
  have z : level (site (j+1) i)=j+1 := rfl
  omega

/-- Every emitted edge is fresh: its newest endpoint is in the new
row, and the three edge kinds cannot name the same undirected edge. -/
theorem graph_schedule {n : Nat} (p : Row.Program n) {j length : Nat} (lt : j<length) :
    FreshSchedule (slots n j) (graph p length) (graph p j) (scheduled p j) := by
  apply freshSchedule_of_codes _ _ (scheduled_nodup p j)
  · intro e he
    obtain ⟨k,ck,eq⟩ := (scheduled_mem p j _).mp (List.mem_map.mpr ⟨e,he,rfl⟩)
    exact (graph_edges p length _).mpr ⟨j,lt,k,ck,eq⟩
  · intro e he old
    obtain ⟨k,_,eq⟩ := (scheduled_mem p j _).mp (List.mem_map.mpr ⟨e,he,rfl⟩)
    obtain ⟨t,ht,l,_,eq'⟩ := (graph_edges p j _).mp old
    have same : grade (namedEdge j k)=grade (namedEdge t l) := congrArg grade (eq.trans eq'.symm)
    simp only [namedEdge_grade] at same
    omega

theorem graph_advance {n : Nat} (p : Row.Program n) (j : Nat) :
    addEdges (slots n j) (graph p j) (scheduled p j)=graph p (j+1) := by
  have nd (e : SlotEdge (n+1+n)) (he : e∈scheduled p j) : slots n j e.1≠slots n j e.2 := by
    obtain ⟨k,hk,h⟩ := (scheduled_mem p j _).mp (List.mem_map.mpr ⟨e,he,rfl⟩)
    intro eq
    apply namedEdge_offDiag p j k hk
    rw [h]
    exact Sym2.mk_isDiag_iff.mpr eq
  apply edgeSet_injective
  rw [addEdges_edgeSet _ _ _ nd]
  ext e
  simp only [Set.mem_union,Set.mem_ofPred_eq,graph_edges,scheduled_mem]
  constructor
  · rintro (⟨i,hi,k,ck,eq⟩|⟨k,ck,eq⟩)
    · exact ⟨i,by omega,k,ck,eq⟩
    · exact ⟨j,by omega,k,ck,eq⟩
  · rintro ⟨i,hi,k,ck,eq⟩
    by_cases old : i<j
    · exact .inl ⟨i,old,k,ck,eq⟩
    · have same : i=j := by omega
      exact .inr ⟨k,same ▸ ck,same ▸ eq⟩

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
