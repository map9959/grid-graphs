import GridGraphs.Constructions.ResidueTwo.LowerTurnDecode

namespace GridGraphs.ResidueTwoLower.Poly
open Turn

private theorem locally {ch : Chart} {s n t m} (hs : s<ch.size)
    (ok : chartOK ch=true)
    (cover : ∀ v d, forced n m v d → allowed ch 0 d t v) :
    let layer := fun r v d => forced n m v d ∧ allowed ch r d t v
    Step n m (layer s) (layer (s+1)) := by
  simp [chartOK] at ok
  have go (v : Pt) (d e : Dir) (b : Bool) (f : forced n m v d)
      (g : forced n m (advance v d) e)
      (a : allowed ch (if b then s+1 else s) e t (advance v d))
      (test : check (trial ch s d e b)=true) : allowed ch (s+1) d t v := by
    by_contra neg
    apply check_sound test t v.1 v.2
    have p := cover _ _ f
    have q := cover _ _ g
    cases d <;> simp_all [trial,Lit.Holds,allowed,advance,offset,sub_eq_add_neg]
  have member (d : Dir) : d∈dirs := by cases d <;> simp [dirs]
  constructor
  · intro v d f ⟨g,a⟩
    exact ⟨f,go v d d true f g a (ok s hs d (member d)).1.1⟩
  · intro v d e he f ⟨g,a⟩
    rcases he with rfl|rfl
    · exact ⟨f,go v d _ false f g a (ok s hs d (member d)).1.2⟩
    · exact ⟨f,go v d _ false f g a (ok s hs d (member d)).2⟩

/-- Sound chart checker: the only physical inclusion needed is that every
forced physical edge is in its direction's first chart region. -/
theorem routes_of_chart {ch : Chart} {n : Nat} {t : ℤ} (m : Mask) (pos : ch.size>0)
    (ok : chartOK ch=true)
    (cover : ∀ v d, forced n m v d → allowed ch 0 d t v)
    (r c : Fin (n-1)) : (holeDual n m).Reachable (.cell r c) .out := by
  let L : Nat → Layer := fun s v d => forced n m v d ∧ allowed ch s d t v
  have first : L 0 = forced n m := by
    funext v d; exact propext ⟨And.left,fun h => ⟨h,cover _ _ h⟩⟩
  have last : L ch.size = fun _ _ => False := by
    funext v d
    simp [L,allowed,Reg,Region.eval]
  let seq (i len : Nat) := (List.range' i len).map L
  have steps (i len : Nat) (h : i+len≤ch.size) :
      List.Forall₂ (Step n m) (seq i len) (seq (i+1) len) := by
    induction len generalizing i with
    | zero => exact .nil
    | succ len ih =>
      simp only [seq,List.range'_succ,List.map_cons]
      exact .cons (locally (by omega) ok cover) (ih _ (by omega))
  let len := ch.size-1
  have eq : len+1=ch.size := by dsimp [len]; omega
  have h := steps 0 (len+1) (by omega)
  have a : seq 0 (len+1) = forced n m :: seq 1 len := by simp [seq,List.range'_succ,first]
  have b : seq 1 (len+1) = seq 1 len ++ [fun _ _ => False] := by
    simp [seq,List.range'_concat,last,show 1+len=ch.size by omega]
  rw [a,show 0+1=1 by decide,b] at h
  exact routes_of_layers n m _ h r c

end GridGraphs.ResidueTwoLower.Poly
