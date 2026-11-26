import GridGraphs.ResidueTwoUpper.TwoGapFrontierExtend

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph

abbrev Pair := Fin 19 × Fin 19
def rowEdgesAt (old m teeth : Nat) (i : Nat) : List Pair :=
  let ix j := Fin.ofNat 19 j
  (if old<512 && (old ||| m).testBit i then [(ix i,ix (10+i))] else []) ++
  (if i>0 && (m.testBit (i-1) || m.testBit i) then [(ix (9+i),ix (10+i))] else []) ++
  (if (m &&& teeth).testBit i then [(ix (10+i),ix 9)] else [])

def rowEdges (old m teeth : Nat) := (List.range 9).flatMap (rowEdgesAt old m teeth)
abbrev Work := Array Nat × Array Nat
def update (w : Work) (e : Pair) := link w.1 w.2 e.1 e.2
def addEdge (port : Fin 19 → V) (H : SimpleGraph V) (e : Pair) :=
  H ⊔ edge (port e.1) (port e.2)

private def block (old m teeth i : Nat) (w : Work) : Option Work := do
  let mut (p,t) := w
  if old<512 && (old ||| m).testBit i then (p,t) ← link p t i (10+i)
  if i>0 && (m.testBit (i-1) || m.testBit i) then (p,t) ← link p t (9+i) (10+i)
  if (m &&& teeth).testBit i then (p,t) ← link p t (10+i) 9
  return (p,t)

private theorem block_eq (old m teeth i : Nat) (hi : i<9) (w : Work) :
    block old m teeth i w=(rowEdgesAt old m teeth i).foldlM update w := by
  rcases w with ⟨p,t⟩
  unfold block rowEdgesAt
  split_ifs <;> simp [List.foldlM_cons,update,Fin.val_ofNat,Nat.mod_eq_of_lt
    (show i<19 by omega),Nat.mod_eq_of_lt (show 10+i<19 by omega),
    Nat.mod_eq_of_lt (show 9+i<19 by omega)]

private theorem for_edges (old m teeth : Nat) (ls : List Nat) (inside : ∀ i∈ls,i<9) (w : Work) :
    forIn (m:=Option) ls w (fun i a => ForInStep.yield <$> block old m teeth i a) =
      (ls.flatMap (rowEdgesAt old m teeth)).foldlM update w := by
  induction ls generalizing w with
  | nil => rfl
  | cons i ls ih =>
    rw [List.flatMap_cons,List.foldlM_append,List.forIn_cons]
    rw [←block_eq _ _ _ _ (inside i (by simp)) w]
    cases h : block old m teeth i w with
    | none => rfl
    | some z => exact ih (fun j hj => inside j (by simp [hj])) z

theorem advance_decompose (s : Frontier) (m teeth : Nat) :
    advance s m teeth = (rowEdges s.last m teeth).foldlM update
      (extendP s.parts,extendT s.tags m) >>= fun w => finishRow w.1 w.2 m := by
  unfold advance rowEdges
  rw [←for_edges _ _ _ _ (fun _ hi => List.mem_range.mp hi)]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  change (forIn (m:=Option) (List.range' 0 ([:9] : Std.Legacy.Range).size) _ _ >>= _) = _
  rw [show List.range' 0 ([:9] : Std.Legacy.Range).size=List.range 9 by decide]
  apply congrArg₂ Bind.bind
  · apply congrArg (forIn (m:=Option) (List.range 9) (extendP s.parts,extendT s.tags m))
    funext i w
    rcases w with ⟨p,t⟩
    unfold block
    split_ifs <;> simp [Functor.map,Option.map_eq_bind,Option.bind_assoc]
  · funext w
    unfold finishRow live
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    rfl

def Fresh (T : SimpleGraph V) (port : Fin 19 → V) (H : SimpleGraph V) : List Pair → Prop
  | [] => True
  | e::es => T.Adj (port e.1) (port e.2) ∧ ¬H.Adj (port e.1) (port e.2) ∧
    Fresh T port (addEdge port H e) es

private theorem run_survives (T : SimpleGraph V) (forest : T.IsAcyclic) (port : Fin 19 → V)
    (ev : Fin 2 → V → Prop) (es : List Pair) (H : SimpleGraph V) (sub : H≤T) (w : Work)
    (model : Models H port ev w.1 w.2) (fresh : Fresh T port H es) :
    ∃ w', es.foldlM update w=some w' ∧ Models (es.foldl (addEdge port) H) port ev w'.1 w'.2 := by
  induction es generalizing H w with
  | nil => exact ⟨w,rfl,model⟩
  | cons e es ih =>
    obtain ⟨a,b,c⟩ := fresh
    obtain ⟨p,t,h,m⟩ := link_survives forest sub model e.1 e.2 a b
    obtain ⟨z,hz,mod⟩ := ih _ (sup_le sub ((edge_le_iff T).mpr (.inr a))) (p,t) m c
    exact ⟨z,by simpa [List.foldlM_cons,update,h] using hz,mod⟩

/-- Survival of the actual imperative `advance`, not a substitute checker.
The exact component/flag model is carried to the returned frontier. -/
theorem advance_survives (T H : SimpleGraph V) (forest : T.IsAcyclic) (sub : H≤T)
    (port : Fin 19 → V) (ev : Fin 2 → V → Prop) (s : Frontier) (m teeth : Nat)
    (model : Models H (port ∘ oldSlot) ev s.parts s.tags) (inj : Function.Injective port)
    (iso : ∀ i y, ¬H.Adj (port (newSlot i)) y)
    (flags : ∀ i (d : Fin 2), (flag m i.val).testBit d ↔ ev d (port (newSlot i)))
    (fresh : Fresh T port H (rowEdges s.last m teeth))
    (escape : Escape ((rowEdges s.last m teeth).foldl (addEdge port) H) port ev) :
    ∃ next, advance s m teeth=some next ∧ next.last=m ∧
      Models ((rowEdges s.last m teeth).foldl (addEdge port) H)
        (port ∘ retained) ev next.parts next.tags := by
  obtain ⟨w,h,ok⟩ := run_survives T forest port ev _ H sub
    (extendP s.parts,extendT s.tags m) (extend_models model inj iso flags) fresh
  obtain ⟨next,r,hl,mt⟩ := retire_survives m ok escape
  exact ⟨next,by simp [advance_decompose,h,r],hl,mt⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
