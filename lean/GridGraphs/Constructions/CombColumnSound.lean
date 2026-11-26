import GridGraphs.Constructions.CombMergeSound

namespace GridGraphs.CombWord
open SimpleGraph

/-- Four new cap sites are isolated before processing this column. -/
structure FreshColumn {V : Type*} (G : SimpleGraph V) (port : Nat → V) : Prop where
  different : ∀ i < 6, ∀ j : Fin 4, port i ≠ port (6+j.val)
  injective : Function.Injective (fun j : Fin 4 => port (6+j.val))
  isolated : ∀ j : Fin 4, ∀ v, ¬ G.Adj (port (6+j.val)) v

theorem extend_column {V : Type*} {G : SimpleGraph V} {port : Nat → V}
    {p : List Nat} (hp : ExtendsLabels G port p) (hlen : p.length = 6)
    (fresh : FreshColumn G port) : ExtendsLabels G port (p++[6,7,8,9]) := by
  classical
  obtain ⟨c,hc,hp⟩ := hp
  let New := fun v => ∃ j : Fin 4, port (6+j.val) = v
  let label := fun v => if h : New v then 6+h.choose.val else c v
  have onNew (j : Fin 4) : label (port (6+j.val)) = 6+j.val := by
    have h : New (port (6+j.val)) := ⟨j,rfl⟩
    have eq := fresh.injective h.choose_spec
    simp [label,dif_pos h,eq]
  refine ⟨label,?_,?_⟩
  · intro x y edge
    have hx : ¬ New x := fun ⟨j,h⟩ => fresh.isolated j y (h ▸ edge)
    have hy : ¬ New y := fun ⟨j,h⟩ => fresh.isolated j x (h ▸ edge.symm)
    simp [label,hx,hy,hc edge]
  · intro i a ha
    by_cases hi : i < 6
    · have h : ¬ New (port i) := fun ⟨j,eq⟩ => fresh.different i hi j eq.symm
      rw [List.getElem?_append_left (by omega)] at ha
      simp [label,h,hp _ _ ha]
    · rw [List.getElem?_append_right (by omega),hlen] at ha
      have bound : i-6 < 4 := by
        have := List.getElem?_eq_some_iff.mp ha
        simpa using this.1
      let j : Fin 4 := ⟨i-6,bound⟩
      have h : i=6+j.val := by dsimp [j]; omega
      have val : a=i := by
        have top : i ≤ 9 := by omega
        clear j h label onNew
        interval_cases i <;> simp_all
      rw [val,h,onNew]

private theorem mapM_lookup {xs p q : List Nat}
    (h : xs.mapM (fun i => p[i]?) = some q) :
    q.length = xs.length ∧ ∀ (i a : Nat), q[i]? = some a →
      ∃ j : Nat, xs[i]? = some j ∧ p[j]? = some a := by
  induction xs generalizing q with
  | nil => simp at h; subst q; simp
  | cons x xs ih =>
    cases hx : p[x]? with
    | none => simp [List.mapM_cons,hx] at h
    | some v =>
      cases ht : xs.mapM (fun i => p[i]?) with
      | none => simp [List.mapM_cons,hx,ht] at h
      | some vs =>
        simp [List.mapM_cons,hx,ht] at h
        subst q
        obtain ⟨hl,hget⟩ := ih ht
        refine ⟨by simp [hl],?_⟩
        intro i a ha
        cases i with
        | zero => simp_all
        | succ i => exact hget i a ha

/-- Retired vertices stay in the graph. Relabel the *whole* graph by
first occurrence among the six retained component names. -/
theorem retire_column {V : Type*} {G : SimpleGraph V} {port : Nat → V}
    {p q : List Nat} (hp : ExtendsLabels G port p)
    (h : retained.mapM (fun i => p[i]?) = some q) :
    ExtendsLabels G (fun i => port (retained[i]?.getD 0)) (q.map q.idxOf) := by
  obtain ⟨c,hc,hp⟩ := hp
  refine ⟨fun x => q.idxOf (c x), fun {_ _} e => congrArg q.idxOf (hc e), ?_⟩
  intro i a ha
  rw [List.getElem?_map] at ha
  cases hi : q[i]? with
  | none => simp [hi] at ha
  | some b =>
    obtain ⟨j,hj,hb⟩ := (mapM_lookup h).2 i b hi
    simpa [hj,hp _ _ hb] using (by simpa [hi] using ha : q.idxOf b = a)

theorem step_graph_sound {V : Type*} {G : SimpleGraph V} {port : Nat → V}
    {s t : Frontier} {m : Nat} (hs : step s m = some t)
    (hf : G.IsAcyclic) (hp : ExtendsLabels G port s.parts)
    (hlen : s.parts.length = 6) (fresh : FreshColumn G port) :
    let G' := (columnEdges s m).foldl (insertPort port) G
    G'.IsAcyclic ∧ t.parts.length = 6 ∧
      ExtendsLabels G' (fun i => port (retained[i]?.getD 0)) t.parts := by
  dsimp only
  simp only [step, Option.bind_apply, Option.bind_eq_some_iff] at hs
  obtain ⟨_,_,_,_,_,_,p,he,q,hq,eq⟩ := hs
  have h := fold_merge_sound port _ hf (extend_column hp hlen fresh) he
  injection eq with eq
  subst t
  exact ⟨h.1, by simp [(mapM_lookup hq).1,retained], retire_column h.2 hq⟩

end GridGraphs.CombWord
