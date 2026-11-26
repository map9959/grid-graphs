import GridGraphs.ResidueTwoUpper.TwoGapCoverageWindow

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
open Catalogue ResidueZero ExitReplay Std.Sat

-- Keep only clauses shared by every base occurrence in a class. This
-- lets one local refutation cover different geometries, not just identical halos.
structure ChartKey where
  k : Nat
  q : Nat
  i : Nat
  j : Nat
  deriving DecidableEq, Inhabited, Repr
def ChartKey.stamp (c : ChartKey) := sig c.k c.q c.i c.j
def level (k j : Nat) := if j<2 then j else if j+3<k then 2 else if j+3=k then 3 else 4
def bucket (c : ChartKey) :=
  if c.q<3 then 10+(c.q-1) else if c.k-4<c.q then 12+(c.k-2-c.q) else
  2*level c.k c.j + (c.i==c.q).toNat
def casesFor (k q : Nat) := if q<3 then [ChartKey.mk k q (q-1) 0] else
  if k-4<q then [ChartKey.mk k q q 0] else
  (List.range (k-1)).flatMap fun j => [ChartKey.mk k q (q-1) j, ChartKey.mk k q q j]
def allKeys := [11,25].flatMap fun k => (List.range (k-2)).flatMap fun t => casesFor k (t+1)
def keys (b : Nat) := allKeys.filter fun c => bucket c==b
def catalogue (b : Nat) : List Band := if b<10 then tables[b/2]! else []

structure Glyph where
  live : Bool
  rim : Option Bool × Nat × Bool
  root : Bool
  exit : Bool
  star : Pos
  patch : Option Pos
  bonds : Fin 4 → Bool
  deriving DecidableEq
def glyph (s : Pos → Stamp) (p : Pos) : Glyph :=
  ⟨onB s p,rimAt s p,rootAt s p,exitAt s p,starPos s p,
   if ∀ i : Fin 9, onB s (plus3 p i) then some (patchPos s p) else none,
   fun d => onB s (shift p d)⟩
def glyphRows (g : Glyph) (p : Pos) : Rows :=
  if g.live then
    (g.rim.1.toList.flatMap (lit (mark p)) ++
     ((List.finRange 4).flatMap fun d => if g.rim.2.1<5 then lit (arrow p d) (decide (g.rim.2.1=d.val)) else []) ++
     (if g.rim.2.2 then guarded (mark p) true (lit (arrow p 3) true) else [])) ++
    ((List.range 5).flatMap fun o => dirRows p o (truth (starW p) fun m =>
      (if g.root then o==4 else o != 4 || m==0) && starOK' g.star g.exit o m)) ++
    ((List.finRange 4).flatMap fun d => (if g.bonds d then bond p d else []) ++
      (List.finRange 4).flatMap fun e => mutex p d e ++ turnRows p d e) ++
    (g.patch.toList.flatMap fun a => truth (patchW p) (patchOK a))
  else lit (mark p) false
theorem glyph_eq (s p) (hp : halo p) : glyphRows (glyph s p) p=atSite s p := by
  simp only [atSite,glyphRows,glyph,core,hp,true_and,if_true,starRows,pins,patchRows]
  by_cases on : onB s p=true <;> by_cases pb : ∀ i : Fin 9, onB s (plus3 p i) <;> simp [on,pb] <;> rfl

def meet (rs : List Rows) : Rows := match rs with
  | [] => []
  | r::rest => rest.foldl (fun acc x => let set := Std.HashSet.ofList x; acc.filter set.contains) r
theorem meet_sub (rs : List Rows) (x : Rows) (hx : x∈rs) : ∀ c∈meet rs, c∈x := by
  cases rs with
  | nil => simp at hx
  | cons r rest =>
    unfold meet
    revert x r
    induction rest with
    | nil => simp_all
    | cons y ys ih =>
      intro x r hx c hc; dsimp only [List.foldl_cons] at hc
      have mem := ih _ _ (List.mem_cons_self : r.filter (Std.HashSet.ofList y).contains ∈ _::ys) c hc
      rcases List.mem_cons.mp hx with rfl|h
      · exact (List.mem_filter.mp mem).1
      rcases List.mem_cons.mp h with rfl|h
      · simpa using (List.mem_filter.mp mem).2
      · exact ih _ _ (List.mem_cons_of_mem _ h) c hc

def commonAt (b : Nat) (p : Pos) :=
  meet ((((keys b).map fun c => glyph c.stamp p).eraseDups).map (glyphRows · p))
def commonRows (b : Nat) := sites.flatMap (commonAt b) ++ (catalogue b).map block
def problem (b : Nat) := formula (commonRows b)

theorem common_sound {c l} (hc : c∈allKeys) (L : Local c.stamp l)
    (unsat : (problem (bucket c)).Unsat) : band (four l) ∈ catalogue (bucket c) := by
  by_contra no; apply impossible _ unsat (value l)
  rw [commonRows,holds_append,holds_flat]
  constructor
  · intro p hp clause hm
    have hg : glyphRows (glyph c.stamp p) p ∈ (((keys (bucket c)).map fun z => glyph z.stamp p).eraseDups.map (glyphRows · p)) := by
      apply List.mem_map.mpr
      refine ⟨_,List.mem_eraseDups.mpr (List.mem_map.mpr ⟨c,?_,rfl⟩),rfl⟩
      simp [keys,hc]
    have mem := meet_sub _ _ hg clause hm
    have hh : halo p := by
      simp [sites] at hp; obtain ⟨r,hr,w,hw,rfl⟩ := hp; unfold halo; dsimp; omega
    rw [glyph_eq _ _ hh] at mem
    exact site_sound L p _ mem
  · intro x hx; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    have bd : ∀ i : Fin 5, ∀ a ∈ tables[i.val]!, bounded a := by unfold bounded; native_decide
    have h := hb; unfold catalogue at h; split at h
    · rename_i hi; exact block_sound l b (bd ⟨_,by omega⟩ _ h) (fun eq => no (eq ▸ hb))
    · contradiction

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
