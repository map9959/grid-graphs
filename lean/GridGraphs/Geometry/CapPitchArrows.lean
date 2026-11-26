import GridGraphs.Geometry.PaddedCapBill

namespace GridGraphs.CapBill
open SimpleGraph Finset

def tooth {r h} (i : Fin r) : Cell r h :=
  (⟨0,by omega⟩,⟨3*i.val+1,by omega⟩)
def owner {r : Nat} (x : Fin (3*r)) : Fin r := ⟨x.val/3,by omega⟩
def rim {r h} (x : Fin (3*r)) : Cell r h := (⟨0,by omega⟩,x)

theorem terminal_eq {r h} {F : Finset (Cell r h)} (pad : Padded F) :
    terminalSet F = univ.image (tooth (h:=h)) := by
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨hf,h0⟩ := mem_filter.mp hv
    have phase := pad.top v hf h0
    refine mem_image.mpr ⟨owner v.2, mem_univ _,Prod.ext (Fin.ext h0.symm) (Fin.ext ?_)⟩
    change 3*(v.2.val/3)+1=v.2.val; omega
  · rw [card_image_of_injective _ (by intro i j eq; apply Fin.ext
                                      have e := congrArg (fun v : Cell r h => v.2.val) eq
                                      dsimp [tooth] at e; omega),card_univ,Fintype.card_fin]
    exact pad.teeth.ge

theorem tooth_mark {r h} {F : Finset (Cell r h)} (pad : Padded F) (i : Fin r) :
    tooth i ∈ F := by
  have mem : tooth i ∈ terminalSet F := (terminal_eq pad) ▸ mem_image_of_mem _ (mem_univ i)
  exact (mem_filter.mp mem).1

private theorem no_diag {r h} {F : Finset (Cell r h)} (pad : Padded F)
    {a b : Cell r h} (ha : a∈F) (hb : b∈F)
    (yd : a.1.val+1=b.1.val ∨ b.1.val+1=a.1.val)
    (xd : a.2.val+1=b.2.val ∨ b.2.val+1=a.2.val) : False := by
  let c : Cell r h := (a.1,b.2)
  let d : Cell r h := (b.1,a.2)
  have ac : (board r h).Adj a c := Or.inl ⟨rfl,xd⟩
  have cb : (board r h).Adj c b := Or.inr ⟨rfl,yd⟩
  have bd : (board r h).Adj b d := Or.inl ⟨rfl,xd.symm⟩
  have da : (board r h).Adj d a := Or.inr ⟨rfl,yd.symm⟩
  have diff : a.1≠b.1 := by intro e; rw [e] at yd; omega
  have cd : c ≠ d := by
    intro eq; have e := congrArg Prod.fst eq; exact diff e
  have := fourCycle_has_unforced_edge ac cb bd da (fun eq => diff (congrArg Prod.fst eq))
    cd pad.forest
  tauto

abbrev bonds {r h} (F : Finset (Cell r h)) := forcedEdgeGraph (board r h) (↑F : Set _)
noncomputable abbrev capDest {r h} (F : Finset (Cell r h)) :=
  chooseRoot (bonds F) (terminalSet F) F
noncomputable abbrev arrow {r h} (F : Finset (Cell r h)) :=
  parent (capDest F) (root_class _ _ _)

theorem no_diagonal_marks {r h} {F : Finset (Cell r h)} (pad : Padded F)
    {a b : Cell r h} (ha : a∈F) (hb : b∈F)
    (yd : a.1.val+1=b.1.val ∨ b.1.val+1=a.1.val)
    (xd : a.2.val+1=b.2.val ∨ b.2.val+1=a.2.val) : False :=
  no_diag pad ha hb yd xd

/-- Both blank sites next to a physical tooth send their unique edge
toward it. A first-free-row mark cannot create a second port there. -/
theorem pitch_leaf {r h} {F : Finset (Cell r h)} (pad : Padded F)
    (x : Fin (3*r)) (hx : x.val%3≠1) :
    arrow F (rim x) = tooth (owner x) := by
  let v : Cell r h := rim x
  let t : Cell r h := tooth (owner x)
  have tm : t ∈ F := tooth_mark pad _
  have vm : v ∉ F := fun f => hx (pad.top v f rfl)
  have gap : x.val+1=t.2.val ∨ t.2.val+1=x.val := by dsimp [t,tooth,owner]; omega
  have inc : (board r h).Adj t v := Or.inl ⟨rfl,gap.symm⟩
  have used : hits (board r h) F v ≠ 0 := by
    have M : t ∈ F.filter (fun a => (board r h).Adj a v) := mem_filter.mpr ⟨tm,inc⟩
    have := card_pos.mpr ⟨_,M⟩
    unfold hits; omega
  have nonroot := mt (blank_fixed (board r h) (terminalSet F) F (filter_subset _ _) vm).mp used
  have e := (parent_step (capDest F) (root_class _ _ _) nonroot).1
  let w := arrow F v
  change (bonds F).Adj v w at e
  have wm : w∈F := e.2.resolve_left vm
  rcases e.1 with ⟨row,col⟩|⟨col,row⟩
  · have z : w.1.val=0 := by rw [←row]; rfl
    have p := pad.top _ wm z
    apply Prod.ext (Fin.ext z) (Fin.ext ?_)
    change w.2.val=t.2.val
    change x.val+1=w.2.val ∨ w.2.val+1=x.val at col
    dsimp [t,tooth,owner]; omega
  · exfalso
    apply no_diag pad tm wm
    · exact row
    · rw [←col]; exact gap.symm

theorem tooth_sends_down {r h} {F : Finset (Cell r h)} (pad : Padded F) (i : Fin r)
    (drop : tooth i ∈ waived (board r h) (terminalSet F) F) :
    arrow F (tooth i) = (⟨1,by omega⟩,(tooth (h:=h) i).2) := by
  classical
  let t : Cell r h := tooth i
  let w := arrow F t
  have st := parent_step (capDest F) (root_class _ _ _) (mem_filter.mp drop).2
  change (bonds F).Adj t w ∧ depth (capDest F) w < depth (capDest F) t at st
  rcases st.1.1 with ⟨row,col⟩|⟨col,row⟩
  · change 3*i.val+1+1=w.2.val ∨ w.2.val+1=3*i.val+1 at col
    have phase : w.2.val%3≠1 := by omega
    have own : owner w.2=i := Fin.ext (by dsimp [owner]; omega)
    have rv : rim w.2=w := Prod.ext row rfl
    have back := pitch_leaf pad w.2 phase
    rw [rv,own] at back
    have nonroot : w≠dest (capDest F) w := by
      intro fix
      have same := (parent_fix (capDest F) (root_class _ _ _) w).mpr fix
      change arrow F w=w at same; rw [back] at same; exact st.1.ne same
    have lower := (parent_step (capDest F) (root_class _ _ _) nonroot).2
    change depth (capDest F) (arrow F w)<_ at lower
    rw [back] at lower
    exact False.elim ((not_lt_of_ge st.2.le) lower)
  · change w = (⟨1,_⟩,t.2)
    refine Prod.ext ?_ (show w.2=t.2 from col.symm)
    apply Fin.ext
    change w.1.val=1
    change 0+1=w.1.val ∨ w.1.val+1=0 at row; omega

end GridGraphs.CapBill
