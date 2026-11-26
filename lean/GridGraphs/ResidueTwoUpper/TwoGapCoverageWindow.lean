import GridGraphs.ResidueTwoUpper.TwoGapCoverageRows

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
open Catalogue ResidueZero ExitReplay Std.Sat

def bond (p : Pos) (d : Fin 4) : Rows :=
  let z := shift p d
  let a := arrow p d
  let b := arrow z ⟨(d.val+2)%4,by omega⟩
  [[(a,false),(b,false)],[(mark p,false),(a,true),(b,true)],[(mark z,false),(a,true),(b,true)],
   [(a,false),(mark p,true),(mark z,true)],[(b,false),(mark p,true),(mark z,true)]]
def turnRows (p : Pos) (d e : Fin 4) :=
  let z := shift p d
  guarded (arrow p d) true (guarded (arrow z e) true
    (branch (sheet p) (lit (sheet z) (wrap d e)) (lit (sheet z) (!wrap d e))))
def mutex (p : Pos) (d e : Fin 4) : Rows :=
  if d=e then [] else [[(arrow p d,false),(arrow p e,false)]]
def pins (s : Pos → Stamp) (p : Pos) : Rows :=
  ((rimAt s p).1.toList.flatMap (lit (mark p))) ++
  ((List.finRange 4).flatMap fun (d : Fin 4) => if (rimAt s p).2.1<5 then lit (arrow p d) (decide ((rimAt s p).2.1=d.val)) else []) ++
  (if (rimAt s p).2.2 then guarded (mark p) true (lit (arrow p 3) true) else [])
instance (p) : Decidable (halo p) := by unfold halo; infer_instance
instance (s p) : Decidable (core s p) := by unfold core halo; infer_instance
def atSite (s : Pos → Stamp) (p : Pos) : Rows :=
  if core s p then pins s p ++ starRows s p ++
    ((List.finRange 4).flatMap fun (d : Fin 4) =>
      (if onB s (shift p d) then bond p d else []) ++
      (List.finRange 4).flatMap fun e => mutex p d e ++ turnRows p d e) ++
    (if ∀ i : Fin 9, onB s (plus3 p i) then patchRows s p else [])
  else if halo p then lit (mark p) false else []

theorem bond_sound {s l} (L : Local s l) (p : Pos) (d : Fin 4) (h : core s p) (z : onB s (shift p d)) :
    Holds (value l) (bond p d) := by
  obtain ⟨ha,hb⟩ := L.bonds p h d z
  simp only [arc,Bool.or_eq_true] at ha hb
  simp [Holds,bond,←Bool.not_eq_true]; tauto
theorem turns_sound {s l} (L : Local s l) (p d e) (h : core s p) :
    Holds (value l) (turnRows p d e) := by
  simp only [turnRows,holds_guarded,val_arrow,decide_eq_true_eq,holds_branch,val_sheet]
  intro a b; have eq := L.turns p h d e a b
  by_cases v : l.sheet p=true <;> simp_all
theorem pins_sound {s l} (L : Local s l) (p) (h : core s p) : Holds (value l) (pins s p) := by
  unfold pins; simp only [holds_append,holds_flat,holds_lit,val_mark,val_arrow]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro b hb; exact L.rim p h b (by simpa using hb)
  · intro d _; split <;> simp_all [L.parents p h]
  · split <;> simp_all [L.tooth p h]
theorem site_sound {s l} (L : Local s l) (p) : Holds (value l) (atSite s p) := by
  unfold atSite; split
  · rename_i h; simp only [holds_append,holds_flat]
    refine ⟨⟨⟨pins_sound L p h,star_sound L p h⟩,?_⟩,?_⟩
    · intro d _; constructor
      · split <;> simp_all [bond_sound L p d h]
      · intro e _; constructor
        · unfold mutex; split <;> simp_all [Holds] <;> omega
        · exact turns_sound L p d e h
    · split <;> simp_all [patch_sound L p h.1]
  · rename_i hc; split
    · rename_i hp; have off : ¬onB s p := fun b => hc ⟨hp,b⟩
      simp [L.off _ hp off]
    · simp

def sites := (List.range 14).flatMap fun r => (List.range 14).map fun c => ((r:Int)-4,(c:Int)-4)
def tw (t : Fin 4) (b : Fin 9) : Wire := mark (3*(t.val%2)+(b.val%3:Nat),3*(t.val/2)+(b.val/3:Nat))
def block (b : Band) : CNF.Clause Wire := (List.finRange 4).flatMap fun t =>
  (List.finRange 9).map fun i => (tw t i, !((![b.1,b.2.1,b.2.2.1,b.2.2.2] t).testBit i))
private theorem test_pack : ∀ f : Fin 9 → Bool, ∀ i : Fin 9, (packed9 f).testBit i=f i := by native_decide
private theorem eq_pack : ∀ (m : Fin 512) (f : Fin 9 → Bool), (∀ i : Fin 9, m.val.testBit i=f i) → m.val=packed9 f := by
  native_decide
def bounded (b : Band) := b.1<512 ∧ b.2.1<512 ∧ b.2.2.1<512 ∧ b.2.2.2<512
theorem block_sound (l : Field) (b : Band) (hb : bounded b) (ne : band (four l)≠b) :
    (block b).eval (value l)=true := by
  by_contra bad
  simp [CNF.Clause.eval,block] at bad
  let v : Fin 4 → Nat := ![b.1,b.2.1,b.2.2.1,b.2.2.2]
  have H (t : Fin 4) : v t=four l t := by
    have lt : v t<512 := by fin_cases t <;> simp_all [v,bounded]
    apply eq_pack ⟨_,lt⟩
    intro i; have h := bad t i
    exact h.symm
  exact ne (by simp only [band,←H]; rfl)
def rows (s : Pos → Stamp) (tab : List Band) := sites.flatMap (atSite s) ++ tab.map block
theorem of_unsat {s l tab} (h : (formula (rows s tab)).Unsat) (bd : ∀ b ∈ tab, bounded b)
    (L : Local s l) : band (four l) ∈ tab := by
  by_contra no
  apply impossible _ h (value l)
  rw [rows,holds_append,holds_flat]
  refine ⟨fun p _ => site_sound L p,?_⟩
  intro c hc; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
  exact block_sound l b (bd b hb) (fun eq => no (eq ▸ hb))

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
