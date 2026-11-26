import GridGraphs.Constructions.CombColumnSound

namespace GridGraphs.CombWord
open SimpleGraph

/-- Column `j` consumes four new vertices at ports 6..9. The previous
four occur at 2..5. The two rail attachment vertices can move with `j`;
they need not be (and on a physical grid are not) single contracted sites. -/
structure RailLayout (V : Type*) (base : SimpleGraph V) where
  port : Nat → Nat → V
  fresh : ∀ j, FreshColumn base (port j)
  future : ∀ j l, j < l → ∀ i (r : Fin 4), port j i ≠ port l (6+r.val)
  shift : ∀ j i, i < 6 → base.Reachable
    (port (j+1) i) (port j (retained[i]?.getD 0))

def lay {V : Type*} (port : Nat → Nat → V) (j : Nat) (s : Frontier)
    (G : SimpleGraph V) : List Nat → SimpleGraph V
  | [] => G
  | m :: ms =>
    lay port (j+1) ⟨(s.phase+1)%3,false,m,[]⟩
      ((columnEdges s m).foldl (insertPort (port j)) G) ms

private theorem lay_parts {V : Type*} (port : Nat → Nat → V) (j : Nat)
    (s : Frontier) (p : List Nat) (G : SimpleGraph V) (w : List Nat) :
    lay port j {s with parts := p} G w = lay port j s G w := by
  cases w <;> rfl

private theorem keep_base {V : Type*} (port : Nat → V) (es : List (Nat × Nat))
    (G : SimpleGraph V) : G ≤ es.foldl (insertPort port) G := by
  induction es generalizing G with
  | nil => rfl
  | cons e es ih => exact le_trans le_sup_left (ih (insertPort port G e))

private theorem keep_isolated {V : Type*} (port : Nat → V) (es : List (Nat × Nat))
    {z : V} (apart : ∀ i, port i ≠ z) {G : SimpleGraph V}
    (isol : ∀ v, ¬G.Adj z v) : ∀ v, ¬(es.foldl (insertPort port) G).Adj z v := by
  induction es generalizing G with
  | nil => exact isol
  | cons e es ih =>
    apply ih
    intro v h
    rcases h with hg | he
    · exact isol v hg
    · rcases ((edge_adj _ _ _ _).mp he).1 with ⟨hz,_⟩ | ⟨hz,_⟩ <;> exact apart _ hz.symm

private theorem labels_move {V : Type*} {G : SimpleGraph V} {port next : Nat → V}
    {p : List Nat} (hp : ExtendsLabels G port p)
    (move : ∀ i, i < p.length → G.Reachable (next i) (port i)) :
    ExtendsLabels G next p := by
  obtain ⟨c,hc,ha⟩ := hp
  refine ⟨c,@hc,?_⟩
  intro i a hi
  obtain ⟨w⟩ := move i (List.getElem?_eq_some_iff.mp hi).1
  suffices ∀ {x y}, G.Walk x y → c x = c y from (this w).trans (ha _ _ hi)
  intro x y w
  induction w with
  | nil => rfl
  | cons e _ ih => exact (hc e).trans ih

/-- Unbounded column induction. All edges are accumulated on the *original*
vertex type; retiring ports never takes an induced subgraph. -/
theorem lay_sound {V : Type*} {base : SimpleGraph V} (L : RailLayout V base)
    (w : List Nat) {s t : Frontier} {j : Nat} {G : SimpleGraph V}
    (accept : run s w = some t) (forest : G.IsAcyclic) (sub : base ≤ G)
    (labels : ExtendsLabels G (L.port j) s.parts) (six : s.parts.length = 6)
    (fresh : ∀ l ≥ j, FreshColumn G (L.port l)) :
    (lay L.port j s G w).IsAcyclic := by
  induction w generalizing s j G with
  | nil => exact forest
  | cons m ms ih =>
    cases hs : step s m with
    | none => simp [run,List.foldlM_cons,hs] at accept
    | some u =>
      have tail : run u ms = some t := by simpa [run,List.foldlM_cons,hs] using accept
      obtain ⟨hf,hlen,hp⟩ := step_graph_sound hs forest labels six (fresh j le_rfl)
      have sub' := sub.trans (keep_base (L.port j) (columnEdges s m) G)
      have updated : {u with parts := []} = ⟨(s.phase+1)%3,false,m,[]⟩ := by
        simp only [step, Option.bind_apply, Option.bind_eq_some_iff] at hs
        obtain ⟨_,_,_,_,_,_,_,_,_,_,he⟩ := hs
        injection he with he
        subst u; rfl
      rw [lay, ← updated, lay_parts]
      apply ih tail hf sub' (labels_move hp fun i hi =>
        (L.shift j i (by omega)).mono sub') hlen
      intro l hl
      have old := fresh l (by omega)
      exact ⟨old.different, old.injective, fun r => keep_isolated _ _
        (fun i => L.future j l (by omega) i r) (old.isolated r)⟩

theorem accepted_layout_forest {V : Type*} {base : SimpleGraph V}
    (L : RailLayout V base) (hf : base.IsAcyclic)
    (labels : ExtendsLabels base (L.port 0) start.parts) {w : List Nat}
    (ok : (run start w).isSome) : (lay L.port 0 start base w).IsAcyclic := by
  obtain ⟨_, ht⟩ := Option.isSome_iff_exists.mp ok
  exact lay_sound L w ht hf le_rfl labels rfl (fun l _ => L.fresh l)

end GridGraphs.CombWord
