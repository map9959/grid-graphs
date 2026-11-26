import GridGraphs.NoPitch.PhysicalKeys
import GridGraphs.NoPitch.ColumnProjection
import GridGraphs.Results.PitchUpper

namespace GridGraphs.NoPitch.LineKeys
open PitchCut Keys GridGraphs.NoPitch.Dual Finset

/-- Forward language at a fixed column. Contains both legitimate starts,
with the same blank guards and final-state test as the physical run. -/
def allowedStep (t : Nat) (s : State) (a : Letter) :=
  (t≠0 || !a.l) && (t != 6 || !a.r) && allows s a (t==6)
def states : Nat → Finset State
  | 0 => {start false,start true}
  | n+1 => (states n).biUnion fun s =>
      (univ.filter fun a => allowedStep n s a).image (advance s)
def key (row : Fin 7) (t : Nat) (s u : State) :=
  8*((pack [axis 19 8 (3*row.val),if t=0 then 0 else axis 19 8 (3*t-3)+1,axis 19 8 (3*t)]*90+
    Keys.state s)*90+Keys.state u)+3

def allKeys (D : Chart) :=
  let idx := index D
  decide (∀ (row t : Fin 7), ∀ s∈states t.val, ∀ a : Letter, allowedStep t.val s a →
    (locate D idx (key row t.val s (advance s a))).isSome=true)

private theorem pass_at (F : Finset (Site 6)) (v : Fin 19) (np : ¬Pitch F v)
    (t : Fin 7) : allowedStep t.val (prefixState F v t.val) (letter F v t.val) := by
  obtain ⟨n,hn,_⟩ := physical_line F v np
  have advance_run (i len : Nat) (eq : i+len=7) (h : i≤t.val)
      (hr : ∃ n, run (prefixState F v i) ((List.range' i len).map (letter F v))=some n) :
      allows (prefixState F v t.val) (letter F v t.val) (t.val==6) := by
    induction len generalizing i with
    | zero => have := t.isLt; omega
    | succ len ih =>
      obtain ⟨b,hb⟩ := hr
      rw [List.range'_succ,List.map_cons,run] at hb
      simp only [Option.bind_apply,Option.bind_eq_some_iff,Option.pure_apply,Option.some.injEq] at hb
      obtain ⟨_,guarded,c,rest,_⟩ := hb
      by_cases same : i=t.val
      · subst i
        have flag : ((List.range' (t.val+1) len).map (letter F v)).isEmpty=(t.val==6) := by
          cases len <;> simp_all [List.range'_succ]; omega
        rw [flag] at guarded
        by_contra! no; simp [guard,no] at guarded
      · exact ih (i+1) (by omega) (by omega) ⟨c,rest⟩
  have pass := advance_run 0 7 rfl (Nat.zero_le _) ⟨n,by simpa [word,List.range_eq_range',prefixState] using hn⟩
  have left : t.val=0 → (letter F v t.val).l=false := by intro e; simp [letter,e]
  have right : t.val=6 → (letter F v t.val).r=false := by intro e; simp [letter,e,bit,N]
  simp only [allowedStep,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,
    bne_iff_ne,pass,and_true]
  tauto

theorem physical_step (S : Finset (Site 6)) (v : Fin 19) (np : ¬Pitch S v) (t : Fin 7) :
    prefixState S v t.val ∈ states t.val ∧
      allowedStep t.val (prefixState S v t.val) (letter S v t.val) := by
  have before (n : Nat) (hn : n≤6) : prefixState S v n∈states n := by
    induction n with
    | zero => unfold prefixState states; cases containsActive (word S v) <;> simp
    | succ n ih =>
      apply mem_biUnion.mpr
      refine ⟨_,ih (by omega),mem_image.mpr ⟨letter S v n,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩⟩
      exact pass_at S v np ⟨n,by omega⟩
  exact ⟨before t.val (by omega),pass_at S v np t⟩

theorem line_found (D : Chart) (ok : allKeys D) (F : Finset (Site 6)) (g : Fin 8) (r t : Fin 7)
    (np : ¬Pitch (view F g) (teeth 6 r)) : (locate D (index D) (line F g r t)).isSome := by
  have h := physical_step _ _ np t
  unfold allKeys at ok; simp only [decide_eq_true_eq] at ok
  exact ok r t _ h.1 _ h.2

private theorem pitch_iff (F : Finset (Site 6)) (v : Fin 19) :
    Pitch F v ↔ ∀ c : Fin 19, (v,c)∈F ↔ c.val%3=0 := by
  have teeth_mem : ∀ v c : Fin 19, (v,c)∈rowTeeth 6 v ↔ c.val%3=0 := by decide +kernel
  constructor
  · intro h c; rw [←teeth_mem,←h]; simp
  · intro h; ext ⟨u,c⟩
    by_cases eq : u=v
    · subst u; rw [teeth_mem,←h]; simp
    · simp [rowTeeth,eq,Ne.symm eq]

private def swapped (g : Fin 8) := g.val%2==1
private def point (g : Fin 8) (r : Fin 19) :=
  let a := small 19 (invers g) (r,0)
  if swapped g then a.2 else a.1

private theorem geom : ∀ (g : Fin 8) (r c : Fin 19), let x := if swapped g then
    (c,point g r) else (point g r,c)
    (small 19 g x).1=r ∧ ((small 19 g x).2.val%3=0 ↔ c.val%3=0) := by decide +kernel
private theorem inject : ∀ g : Fin 8, Function.Injective (small 19 g) := by
  have inv : ∀ (g : Fin 8) (x : Site 6), small 19 (invers g) (small 19 g x)=x := by decide +kernel
  intro g; exact Function.LeftInverse.injective (inv g)

theorem rotated_no_pitch (F : Finset (Site 6)) (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v))
    (g : Fin 8) (r : Fin 19) : ¬Pitch (view F g) r := by
  intro pitch
  have line := (pitch_iff _ _).mp pitch
  have char (c : Fin 19) :
      (if swapped g then (c,point g r) else (point g r,c))∈F ↔ c.val%3=0 := by
    let x := if swapped g then (c,point g r) else (point g r,c)
    have xy : (small 19 g x).1=r ∧ ((small 19 g x).2.val%3=0 ↔ c.val%3=0) := geom g r c
    have e := line (small 19 g x).2
    rw [←xy.1] at e
    have iff : small 19 g x∈view F g ↔ x∈F := by
      constructor
      · intro h; obtain ⟨y,m,eq⟩ := mem_image.mp h; exact inject g eq ▸ m
      · exact mem_image_of_mem _
    exact iff.symm.trans (e.trans xy.2)
  cases rev : swapped g with
  | false => exact np _ (.inl ((pitch_iff ..).mpr fun c => by simpa [rev] using char c))
  | true =>
    apply np (point g r) (.inr ((pitch_iff (transpose F) (point g r)).mpr ?_))
    intro c
    have h : ((point g r,c)∈transpose F ↔ (c,point g r)∈F) := by
      constructor
      · intro mem; obtain ⟨y,hy,eq⟩ := mem_image.mp mem
        have same : y=(c,point g r) := congrArg Prod.swap eq
        rwa [←same]
      · exact fun m => mem_image_of_mem Prod.swap m
    exact h.trans (by simpa [rev] using char c)

end GridGraphs.NoPitch.LineKeys
