import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripBackward

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan

private def index {L : Type} [BEq L] [Hashable L] (table : List (L × L)) :
    Std.HashMap L (List L) :=
  table.foldr (fun (a,b) m => m.insert a (b :: m.getD a [])) (Std.HashMap.emptyWithCapacity)

private theorem index_lookup {L : Type} [BEq L] [Hashable L] [LawfulBEq L]
    (table : List (L × L)) (a : L) :
    (index table).getD a []=table.filterMap (fun (b,c) => if b==a then some c else none) := by
  induction table with
  | nil => simp [index,Std.HashMap.getD_emptyWithCapacity]
  | cons e es ih =>
    obtain ⟨b,c⟩ := e
    simp only [index,List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert,List.filterMap_cons]
    by_cases eq : b=a
    · subst b; simp [ih]
    · simp [eq,ih]

private theorem filterMap_index {L A : Type} [BEq L] [Hashable L] [LawfulBEq L] [DecidableEq L]
    (table : List (L × L)) (a : L) (f : L → Option A) :
    ((index table).getD a []).filterMap f =
      table.filterMap (fun (b,c) => if a=b then f c else none) := by
  rw [index_lookup]
  induction table with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨b,c⟩ := e
    by_cases eq : a=b
    · subst b; simp only [List.filterMap_cons,beq_self_eq_true,if_true,ih]
    · simpa [eq,Ne.symm eq] using ih

def indexedStep {L S : Type} [BEq L] [Hashable L]
    (table : List (L × L)) (step : L → L → S → Option S)
    (current : List (L × S)) : List (L × S) :=
  let m := index table
  current.flatMap fun (a,s) => (m.getD a []).filterMap fun c => (step a c s).map (c,·)

theorem indexedStep_eq {L S : Type} [BEq L] [Hashable L] [LawfulBEq L] [DecidableEq L]
    (table : List (L × L)) (step : L → L → S → Option S) (current : List (L × S)) :
    indexedStep table step current=forwardStep table step current := by
  simp only [indexedStep,forwardStep]
  congr 1
  funext p
  obtain ⟨a,s⟩ := p
  exact filterMap_index _ _ _

def indexedArcs {L S : Type} [BEq L] [Hashable L] [BEq S] [Hashable S]
    (table : List (L × L)) (step : L → L → S → Option S)
    (current live : List (L × S)) : List (Arc L S) :=
  let m := index table
  let keep := live.foldl Std.HashSet.insert Std.HashSet.emptyWithCapacity
  (current.flatMap fun (a,x) => (m.getD a []).filterMap fun c =>
    (step a c x).map (fun y => ((a,x),(c,y)))).filter (fun a => keep.contains a.2)

private theorem set_fold_mem {A : Type} [BEq A] [Hashable A] [LawfulBEq A]
    (l : List A) (m : Std.HashSet A) (a : A) :
    a ∈ l.foldl Std.HashSet.insert m ↔ a∈m ∨ a∈l := by
  induction l generalizing m with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons,ih,Std.HashSet.mem_insert,beq_iff_eq,List.mem_cons]
    grind

theorem indexedArcs_eq {L S : Type} [BEq L] [Hashable L] [LawfulBEq L] [DecidableEq L]
    [BEq S] [Hashable S] [LawfulBEq S] [DecidableEq S]
    (tables : Nat → List (L × L)) (step : Nat → L → L → S → Option S)
    (current : Nat → List (L × S)) (live : List (L × S)) (j : Nat) :
    indexedArcs (tables j) (step j) (current j) live=backwardArcs tables step current live j := by
  simp only [indexedArcs,backwardArcs,forwardArcs]
  congr 1
  · funext a
    apply Bool.eq_iff_iff.mpr
    simp only [Std.HashSet.contains_iff_mem,decide_eq_true_eq,set_fold_mem,
      Std.HashSet.not_mem_emptyWithCapacity,false_or]
  · congr 1
    funext p
    obtain ⟨a,x⟩ := p
    exact filterMap_index (tables j) a (fun c => (step j a c x).map (fun y => ((a,x),(c,y))))

def indexedLayerArcs {L S : Type} [BEq L] [Hashable L] [BEq S] [Hashable S]
    (tables : Nat → List (L × L)) (step : Nat → L → L → S → Option S)
    (current : Nat → List (L × S)) (live : List (L × S)) (j : Nat) :
    List (Arc L S) := indexedArcs (tables j) (step j) (current j) live

theorem indexedLayerArcs_eq {L S : Type} [BEq L] [Hashable L] [LawfulBEq L] [DecidableEq L]
    [BEq S] [Hashable S] [LawfulBEq S] [DecidableEq S]
    (tables : Nat → List (L × L)) (step : Nat → L → L → S → Option S)
    (current : Nat → List (L × S)) (live : List (L × S)) (j : Nat) :
    indexedLayerArcs tables step current live j=backwardArcs tables step current live j :=
  indexedArcs_eq tables step current live j

private def dedupScan {A : Type} [BEq A] [Hashable A] (xs : List A) : Std.HashSet A × List A :=
  xs.foldr (fun a (s,l) => if s.contains a then (s,l) else (s.insert a,a::l))
    (Std.HashSet.emptyWithCapacity,[])

def indexedDedup {A : Type} [BEq A] [Hashable A] (xs : List A) : List A :=
  (dedupScan xs).2

private theorem dedupScan_cons {A : Type} [BEq A] [Hashable A] (a : A) (xs : List A) :
    dedupScan (a::xs) = if (dedupScan xs).1.contains a then dedupScan xs
      else ((dedupScan xs).1.insert a,a::(dedupScan xs).2) := by
  simp only [dedupScan,List.foldr_cons]
  rfl

private theorem dedupScan_spec {A : Type} [BEq A] [Hashable A] [LawfulBEq A] [DecidableEq A]
    (xs : List A) : (∀ a, a ∈ (dedupScan xs).1 ↔ a ∈ xs) ∧ indexedDedup xs=xs.dedup := by
  induction xs with
  | nil => simp [indexedDedup,dedupScan,Std.HashSet.not_mem_emptyWithCapacity]
  | cons a xs ih =>
    have found : (dedupScan xs).1.contains a=true ↔ a∈xs :=
      Std.HashSet.contains_iff_mem.trans (ih.1 a)
    by_cases mem : a∈xs
    · have hit := found.mpr mem
      simp only [indexedDedup] at ih
      simp only [indexedDedup,dedupScan_cons,hit,if_true,List.dedup_cons_of_mem mem]
      change (∀ b, b∈(dedupScan xs).1 ↔ b∈a::xs) ∧ (dedupScan xs).2=xs.dedup
      exact ⟨fun b => by rw [ih.1]; simp only [List.mem_cons]; grind,ih.2⟩
    · have miss : ¬(dedupScan xs).1.contains a=true := fun yes => mem (found.mp yes)
      simp only [indexedDedup] at ih
      simp only [indexedDedup,dedupScan_cons,miss,List.dedup_cons_of_notMem mem]
      change (∀ b, b∈(dedupScan xs).1.insert a ↔ b∈a::xs) ∧
        a::(dedupScan xs).2=a::xs.dedup
      exact ⟨fun b => by rw [Std.HashSet.mem_insert,beq_iff_eq,ih.1]; simp [eq_comm],
        congrArg (a::·) ih.2⟩

theorem indexedDedup_eq {A : Type} [BEq A] [Hashable A] [LawfulBEq A] [DecidableEq A]
    (xs : List A) : indexedDedup xs=xs.dedup := (dedupScan_spec xs).2

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
