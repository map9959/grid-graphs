import GridGraphs.ResidueTwoUpper.TwoGapFrontierRows

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph Finset ResidueZero Stencil Catalogue
open scoped Sym2

variable {u : Nat}
def previous (F : Finset (Board u)) (l t : Nat) := if t=0 then 512 else wordRow F l t
def insertions (F : Finset (Board u)) (d l t : Nat) :=
  rowEdges (previous F l t) (wordRow F l (t+1)) (pinMask (u:=u) d l (t+1))

theorem enabled0 (F : Finset (Board u)) (d l t : Nat) (i : Fin 9) :
    enabled (previous F l t) (wordRow F l (t+1)) (pinMask (u:=u) d l (t+1)) i 0 ↔
    t≠0 ∧ (rowSite u l t i∈F ∨ rowSite u l (t+1) i∈F) := by
  have h := (packed_iff (fun i => decide (rowSite u l t i∈F))).1
  change wordRow F l t<512 at h
  by_cases z : t=0 <;> simp [enabled,previous,z,h,wordRow_bit]

def prev (i : Fin 9) : Fin 9 := ⟨i.val-1,by omega⟩
theorem enabled1 (F : Finset (Board u)) (d l t : Nat) (i : Fin 9) :
    enabled (previous F l t) (wordRow F l (t+1)) (pinMask (u:=u) d l (t+1)) i 1 ↔
    0 < i.val ∧ (rowSite u l (t+1) (prev i)∈F ∨ rowSite u l (t+1) i∈F) := by
  simp only [enabled,Matrix.cons_val_one,Matrix.cons_val_zero,Bool.and_eq_true,Bool.or_eq_true,
    wordRow_bit F l _ (prev i),wordRow_bit F l _ i,decide_eq_true_eq]
  change (_ ∧ ((wordRow F l (t+1)).testBit (prev i).val=true ∨ _)) ↔ _
  rw [wordRow_bit,decide_eq_true_eq]

theorem enabled2 (F : Finset (Board u)) (d l t : Nat) (i : Fin 9) :
    enabled (previous F l t) (wordRow F l (t+1)) (pinMask (u:=u) d l (t+1)) i 2 ↔
    rowSite u l (t+1) i∈F ∧ ((t+1=2 ∧ l+i.val≠d) ∨ t+1=high u-2) := by
  simp [enabled,wordRow_bit,pinMask,packed_bits]

def endpoints (port : Fin 19 → V) (e : Pair) := s(port e.1,port e.2)

theorem endpoints_nodup (port : Fin 19 → V) (inj : Function.Injective port)
    (old m teeth : Nat) : ((rowEdges old m teeth).map (endpoints port)).Nodup := by
  let all := (List.finRange 9).flatMap fun i => (List.finRange 3).map (directed i)
  -- At i=0 the putative horizontal edge would be a duplicate root
  -- pin, but that edge is never enabled.
  let slots (i : Nat) : List Pair := if h : i<9 then
    let j : Fin 9 := ⟨i,h⟩
    [directed j 0] ++ (if i>0 then [directed j 1] else []) ++ [directed j 2] else []
  have sub (i : Nat) (h : i<9) : (rowEdgesAt old m teeth i).Sublist (slots i) := by
    let j : Fin 9 := ⟨i,h⟩
    have a : Fin.ofNat 19 i=(⟨i,by omega⟩ : Fin 19) := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have b : Fin.ofNat 19 (10+i)=newSlot j := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have c : Fin.ofNat 19 (9+i)=(⟨9+i,by omega⟩ : Fin 19) := Fin.ext (Nat.mod_eq_of_lt (by omega))
    dsimp [rowEdgesAt,slots,directed]
    simp only [dif_pos h]
    split_ifs <;> simp_all [a,b,c,newSlot,j,Fin.ofNat_eq_cast,List.cons_sublist_cons,
      List.sublist_cons_iff] <;> grind
  have subset {ls : List Nat} (h : ∀ i∈ls, i<9) :
      (ls.flatMap (rowEdgesAt old m teeth)).Sublist (ls.flatMap slots) := by
    induction ls with
    | nil => rfl
    | cons a l ih =>
      exact (sub a (h _ (by simp))).append (ih (fun i hi => h i (by simp [hi])))
  have distinct : (((List.range 9).flatMap slots).map (endpoints id)).Nodup := by native_decide
  have incl := (subset (ls:=List.range 9) (fun i => List.mem_range.mp)).map (endpoints id)
  have h := distinct.sublist incl
  have eq : (rowEdges old m teeth).map (endpoints port)=
      ((rowEdges old m teeth).map (endpoints id)).map (Sym2.map port) := by simp [List.map_map]; intros; rfl
  rw [eq]; exact h.map (Sym2.map.injective inj)

theorem fresh_list {T H : SimpleGraph V} (port : Fin 19 → V) (es : List Pair)
    (unique : (es.map (endpoints port)).Nodup)
    (ok : ∀ e∈es, T.Adj (port e.1) (port e.2) ∧ ¬H.Adj (port e.1) (port e.2)) :
    Fresh T port H es := by
  induction es generalizing H with
  | nil => trivial
  | cons e es ih =>
    obtain ⟨new,absent⟩ := ok e (by simp)
    obtain ⟨head,tail⟩ := List.nodup_cons.mp unique
    refine ⟨new,absent,ih tail ?_⟩
    intro f hf
    obtain ⟨a,b⟩ := ok f (by simp [hf])
    refine ⟨a,fun h => ?_⟩
    rcases h with h|h
    · exact b h
    · apply head
      apply List.mem_map.mpr
      refine ⟨f,hf,?_⟩
      rcases (edge_adj ..).mp h with ⟨⟨eq,eq'⟩|⟨eq,eq'⟩,_⟩ <;>
        unfold endpoints <;> rw [eq,eq'] <;> simp [Sym2.eq_swap]

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
