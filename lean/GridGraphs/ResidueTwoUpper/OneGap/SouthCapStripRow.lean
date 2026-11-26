import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripPacked

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph

abbrev SlotEdge (n : Nat) := Fin n × Fin n

def insertEdges {n : Nat} (p : Partition n) : List (SlotEdge n) → Option (Partition n)
  | [] => some p
  | (a,b)::es => (p.insert a b).bind (fun next => insertEdges next es)

def addEdges {V : Type} {n : Nat} (f : Fin n → V) (G : SimpleGraph V) :
    List (SlotEdge n) → SimpleGraph V
  | [] => G
  | (a,b)::es => addEdges f (G ⊔ SimpleGraph.edge (f a) (f b)) es

/-- The edge schedule is precise: no second insertion of an
undirected edge (including a wire), and no nonphysical edges. -/
def FreshSchedule {V : Type} {n : Nat} (f : Fin n → V) (W G : SimpleGraph V) :
    List (SlotEdge n) → Prop
  | [] => True
  | (a,b)::es => W.Adj (f a) (f b) ∧ ¬G.Adj (f a) (f b) ∧
    FreshSchedule f W (G ⊔ SimpleGraph.edge (f a) (f b)) es

theorem insertEdges_reflects {V : Type} {n : Nat}
    {p : Partition n} {G W : SimpleGraph V} {f : Fin n → V} {mark openSite : V → Prop}
    (inv : p.Reflects G f mark openSite) (acy : W.IsAcyclic) (sub : G ≤ W)
    (es : List (SlotEdge n)) (schedule : FreshSchedule f W G es) :
    ∃ next, insertEdges p es=some next ∧ next.Reflects (addEdges f G es) f mark openSite := by
  induction es generalizing G p with
  | nil => exact ⟨p,rfl,inv⟩
  | cons e es ih =>
    obtain ⟨a,b⟩ := e
    obtain ⟨adj,fresh,remaining⟩ := schedule
    obtain ⟨ok,next⟩ := p.insert_reflects inv acy sub adj fresh
    have sub' : G ⊔ SimpleGraph.edge (f a) (f b) ≤ W := by
      apply sup_le sub
      intro x y xy
      rcases ((edge_adj _ _ _ _).mp xy).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact adj
      · exact adj.symm
    obtain ⟨out,done,outInv⟩ := ih next sub' remaining
    exact ⟨out,by rw [insertEdges,ok]; exact done,outInv⟩

def closeRow {n m : Nat} (p : Partition n)
    (old : List (Fin n)) (keep : Fin m → Fin n) : Option PackedPartition :=
  if p.rejectsForgotten old keep then none else some (p.forget keep).pack

def rowCore {n m : Nat} (p : Partition n) (es : List (SlotEdge n))
    (old : List (Fin n)) (keep : Fin m → Fin n) : Option PackedPartition :=
  (insertEdges p es).bind fun next => closeRow next old keep

/-- The physical no-disappearance condition for a row: any old
marked component has an open site (the apex counts as open), or
still touches a retained slot. -/
def RowClosure {V : Type} {n m : Nat} (G : SimpleGraph V) (f : Fin n → V)
    (mark openSite : V → Prop) (old : List (Fin n)) (keep : Fin m → Fin n) : Prop :=
  ∀ x ∈ old, ComponentFlag G mark (f x) →
    ComponentFlag G openSite (f x) ∨ ∃ y, G.Reachable (f (keep y)) (f x)

theorem closeRow_reflects {V : Type} {n m : Nat} {p : Partition n}
    {G : SimpleGraph V} {f : Fin n → V} {mark openSite : V → Prop}
    (inv : p.Reflects G f mark openSite) (hm : m≤16)
    (old : List (Fin n)) (keep : Fin m → Fin n)
    (closure : RowClosure G f mark openSite old keep) :
    ∃ out, closeRow p old keep=some out ∧
      (Partition.unpack m out).Reflects G (f ∘ keep) mark openSite := by
  have keepGoing : p.rejectsForgotten old keep=false := by
    apply Bool.eq_false_iff.mpr
    intro rejects
    obtain ⟨x,hx,hasMark,notOpen,gone⟩ := (p.rejectsForgotten_iff inv old keep).mp rejects
    exact (closure x hx hasMark).elim notOpen (fun ⟨y,r⟩ => gone y r)
  refine ⟨(p.forget keep).pack,by simp [closeRow,keepGoing],?_⟩
  rw [Partition.unpack_pack _ hm (p.forget_canonical inv keep)]
  exact p.forget_reflects inv keep

/-- Successful packed output and the exact induced next-frontier
invariant, with every edge update and the loss-of-class test checked. -/
theorem rowCore_reflects {V : Type} {n m : Nat}
    {p : Partition n} {G W : SimpleGraph V} {f : Fin n → V} {mark openSite : V → Prop}
    (inv : p.Reflects G f mark openSite) (acy : W.IsAcyclic) (sub : G ≤ W)
    (es : List (SlotEdge n)) (schedule : FreshSchedule f W G es) (hm : m≤16)
    (old : List (Fin n)) (keep : Fin m → Fin n)
    (closure : RowClosure (addEdges f G es) f mark openSite old keep) :
    ∃ out, rowCore p es old keep=some out ∧
      (Partition.unpack m out).Reflects (addEdges f G es) (f ∘ keep) mark openSite := by
  obtain ⟨next,h,nextInv⟩ := insertEdges_reflects inv acy sub es schedule
  obtain ⟨out,done,outInv⟩ := closeRow_reflects nextInv hm old keep closure
  exact ⟨out,by rw [rowCore,h]; exact done,outInv⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
