import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayUpdate
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapCatalogueDecode

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
namespace GridScan

def unpackWord (m : Nat) : Word :=
  (m%512,(m/512)%512,(m/512^2)%512,(m/512^3)%512)

private theorem unpack_pack_word {w : Word} (fit : FitsWord w) : unpackWord (packWord w)=w := by
  rcases w with ⟨a,b,c,d⟩
  change a<512 ∧ b<512 ∧ c<512 ∧ d<512 at fit
  simp only [unpackWord,packWord,Prod.mk.injEq]
  norm_num
  exact ⟨by omega,by omega,by omega,by omega⟩

def bankWords (r c : Nat) : List Word :=
  ((packedBank[7*(r-6)+(c-6)]!).toList.map unpackWord) ++ extra r c

theorem bankWords_cover {r c : Nat} {w : Word} (fit : FitsWord w)
    (ok : widened ordinary r c w) : w∈bankWords r c := by
  rcases ok with ord|added
  · obtain ⟨rl,rh,cl,ch,mem⟩ := ord
    have ix : 7*(r-6)+(c-6)<packedBank.size := by rw [packed_bank_size.1]; omega
    simp only [Array.getElem?_eq_getElem ix,Option.any_some] at mem
    apply List.mem_append_left
    refine List.mem_map.mpr ⟨packWord w,?_,unpack_pack_word fit⟩
    rw [getElem!_pos packedBank (7*(r-6)+(c-6)) ix]
    simpa using Array.contains_iff_mem.mp mem
  · exact List.mem_append_right _ added

def initialBank (h : Nat) : Bank :=
  fun r c => (bankWords (endTag h r) (endTag (width h) c)).filter
    (fun w => decide (r≠0 ∨ (w.1=73 ∧ w.2.1=73)))

theorem initialBank_cover {h r c : Nat} {w : Word} (fit : FitsWord w)
    (admit : initialDomains h r c w) : w∈initialBank h r c := by
  apply List.mem_filter.mpr
  refine ⟨bankWords_cover fit admit.1, decide_eq_true ?_⟩
  by_cases e : r=0
  · exact .inr (admit.2 e)
  · exact .inl e

/-- All retained marks are nine-bit masks. Filtering may introduce no
extra physical solutions; soundness only needs the checked inclusion. -/
def FitsTiles (t : Tiles) : Prop := ∀ r c, t r c<512

theorem physical_tiles_fit {n : Nat} (F : Finset (GridGraphs.GridVertex n n))
    (v : L7.View) (k h : Nat) : FitsTiles (cropTiles F v k h) := by
  intro r c
  change FanSlab.square F v (firstRow k h+3*r) (firstCol k h+3*c)<512
  exact (FanSlab.unpack _).1

/-- Materialize each finite array before the next update. No large
domain banks are persisted. -/
def materialize (h : Nat) (D : Bank) : Bank :=
  let rows := Array.ofFn (fun r : Fin (h-1) =>
    Array.ofFn (fun c : Fin (width h-1) => D r.val c.val))
  fun r c =>
    if r+2≤h ∧ c+2≤width h then ((rows[r]?).bind (fun row => row[c]?)).getD []
    else D r c

theorem materialize_eq (h : Nat) (D : Bank) : materialize h D=D := by
  funext r c
  unfold materialize
  split
  · rename_i valid
    simp only [Array.getElem?_ofFn,dif_pos (show r<h-1 by omega),
      Option.bind_some,dif_pos (show c<width h-1 by omega),Option.getD_some]
  · rfl

def emptyCell (h : Nat) (D : Bank) : Option (Nat × Nat) :=
  ((List.range (h-1)).flatMap fun r => (List.range (width h-1)).map (r,·)).find?
    (fun (r,c) => (D r c).isEmpty)

theorem emptyCell_empty {h : Nat} {D : Bank} {r c : Nat} (hit : emptyCell h D=some (r,c)) :
    r+2≤h ∧ c+2≤width h ∧ D r c=[] := by
  obtain ⟨a,ha,m⟩ := List.mem_flatMap.mp (List.mem_of_find?_eq_some hit)
  obtain ⟨b,hb,e⟩ := List.mem_map.mp m
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
  have h₁ := List.mem_range.mp ha
  have h₂ := List.mem_range.mp hb
  have no := List.find?_some hit
  exact ⟨by omega,by omega,List.isEmpty_iff.mp no⟩

def execute {h : Nat} : List (Update h) → Bank → Bool
  | [],D => (emptyCell h D).isSome
  | z::zs,D =>
    if (emptyCell h D).isSome then true
    else execute zs (materialize h (updateBank z D))

theorem execute_cannot_reject {h : Nat} (lo : 14≤h) (zs : List (Update h)) (D : Bank) (t : Tiles)
    (init : Admitted h (width h) (memBank D) t)
    (traces : ∀ z∈zs,
      z.window.HasTrace (tileSweep (3*z.window.depth) z.window.axis
        (replayTooth z.window z.north) (replayExits z.window)) (band t z.window.axis z.window.start)) :
    execute zs D=false := by
  have notEmpty {D : Bank} (ad : Admitted h (width h) (memBank D) t) :
      (emptyCell h D).isSome=false := by
    cases e : emptyCell h D with
    | none => rfl
    | some p =>
      obtain ⟨r,c⟩ := p
      obtain ⟨hr,hc,nil⟩ := emptyCell_empty e
      have mem := ad r c hr hc
      change word t r c∈D r c at mem
      rw [nil] at mem
      exact False.elim (List.not_mem_nil mem)
  induction zs generalizing D with
  | nil => exact notEmpty init
  | cons z zs ih =>
    rw [execute,notEmpty init,if_neg Bool.false_ne_true,materialize_eq]
    have survives := survives_update z.window _ init (traces z (by simp))
    apply ih
    · intro r c hr hc
      exact updateBank_sound z (length_ge2 lo z.window) r c _ (survives r c hr hc)
    · intro z hz
      exact traces z (List.mem_cons_of_mem _ hz)

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
