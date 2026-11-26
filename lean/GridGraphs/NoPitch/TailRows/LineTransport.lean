import GridGraphs.NoPitch.Budget.LineSymmetries

namespace GridGraphs.NoPitch.TailRows
open PitchCut Keys Budget Finset

/-- Reachable prefix automaton before the right boundary is imposed. -/
def moves (ss : Finset State) (first : Bool) := ss.biUnion fun s =>
  (univ.filter fun a : Letter => (!first || !a.l) && allows s a false).image (advance s)
def layers : Nat → Finset State
  | 0 => {start false,start true}
  | n+1 => moves (layers n) (n==0)

theorem stable : layers 5=layers 4 := by decide +kernel
theorem clipped_layers (n : Nat) : layers n=layers (min n 4) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n<4
    · rw [min_eq_left (by omega)]
    · have hn : min n 4=4 := by omega
      change moves (layers n) (n==0)=_
      rw [ih,hn,show (n==0)=false by simp; omega,min_eq_right (by omega)]
      exact stable

def permit (k j : Nat) (s : State) (a : Letter) :=
  (j != 0 || !a.l) && (j != k || !a.r) && allows s a (j==k)

private theorem passes {k} (S : Finset (Site k)) (v : Fin (N k)) (np : ¬Pitch S v) (j : J k) :
    permit k j.val (prefixState S v j.val) (letter S v j.val) := by
  obtain ⟨n,hn,_⟩ := physical_line S v np
  have runAt (i len : Nat) (w : i+len=k+1) (before : i≤j.val)
      (hr : ∃ n, run (prefixState S v i) ((List.range' i len).map (letter S v))=some n) :
      allows (prefixState S v j.val) (letter S v j.val) (j.val==k) := by
    induction len generalizing i with
    | zero => have := j.isLt; omega
    | succ len ih =>
      obtain ⟨_,h⟩ := hr
      rw [List.range'_succ,List.map_cons,run] at h
      simp only [Option.bind_apply,Option.bind_eq_some_iff,Option.pure_apply,Option.some.injEq] at h
      obtain ⟨_,pass,b,tail,_⟩ := h
      by_cases same : i=j.val
      · subst i
        have flag : ((List.range' (j.val+1) len).map (letter S v)).isEmpty=(j.val==k) := by
          cases len <;> simp_all [List.range'_succ] <;> omega
        rw [flag] at pass; by_contra! no; simp [guard,no] at pass
      · exact ih (i+1) (by omega) (by omega) ⟨b,tail⟩
  have p := runAt 0 (k+1) (by omega) (by omega) ⟨n,by simpa [word,List.range_eq_range',prefixState] using hn⟩
  have l : j.val=0 → (letter S v j.val).l=false := by intro e; simp [letter,e]
  have r : j.val=k → (letter S v j.val).r=false := by intro e; simp [letter,e,bit,N]
  simp only [permit,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,Bool.not_eq_true',p,and_true]; tauto

theorem physical_step {k} (S : Finset (Site k)) (v : Fin (N k)) (np : ¬Pitch S v) (j : J k) :
    prefixState S v j.val∈layers (min j.val 4) ∧ permit k j.val (prefixState S v j.val) (letter S v j.val) := by
  have h (n : Nat) (hn : n≤k) : prefixState S v n ∈ layers n := by
    induction n with
    | zero => unfold layers prefixState; cases containsActive (word S v) <;> simp
    | succ n ih =>
      apply mem_biUnion.mpr
      refine ⟨_,ih (by omega),mem_image.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩⟩
      have a := passes S v np ⟨n,by omega⟩
      change permit k n _ _ at a
      simpa [permit,beq_eq_false_iff_ne.mpr (by omega : n≠k),show n≠k by omega] using a
  rw [←clipped_layers]
  exact ⟨h _ (by omega),passes S v np j⟩

def band (k j : Nat) := axis (N k) 8 (3*j)
def prior (k j : Nat) := if j=0 then 0 else band k (j-1)+1
def arcKey (y prev curr : Nat) (s t : State) :=
  8*((pack [y,prev,curr]*90+state s)*90+state t)+3

/-- Compress directly to either base width. Retain the last four slots
because the transition reads both the slot and its predecessor. -/
def rep (k b j : Nat) := if k-j≤3 then b-(k-j) else min j 5

theorem rep_geometry {k b j : Nat} (hb : 19≤b) (hk : b≤k) (hj : j≤k) :
    let u := rep k b j
    u≤b ∧ (u=0 ↔ j=0) ∧ (u=b ↔ j=k) ∧ min u 4=min j 4 ∧
      band b u=band k j ∧ prior b u=prior k j := by
  have bands (l i : Nat) (li : i≤l) : band l i=
      if i≤2 then 3*i else if l-i≤2 then 18-3*(l-i) else 9 := by
    unfold band axis N; split_ifs <;> omega
  let u := rep k b j
  have bounds : u≤b ∧ (u=0 ↔ j=0) ∧ (u=b ↔ j=k) ∧ min u 4=min j 4 := by
    unfold u rep; split <;> omega
  refine ⟨bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2,?_,?_⟩
  · rw [bands _ _ bounds.1,bands _ _ hj]; unfold u rep; split_ifs <;> omega
  · unfold prior
    by_cases z : j=0
    · rw [if_pos (bounds.2.1.mpr z),if_pos z]
    · rw [if_neg (mt bounds.2.1.mp z),if_neg z,bands _ _ (by have := bounds.1; omega),bands _ _ (by omega)]
      unfold rep; split_ifs <;> omega

def before (A : Nat → Nat → State → Int) (k r j : Nat) (s : State) :=
  if j=0 then 0 else A (band k r) (band k (j-1)) s
def after (A : Nat → Nat → State → Int) (k r j : Nat) (t : State) :=
  if j=k then 0 else A (band k r) (band k j) t

/-- Any additive transition price checked at one base transports to
every larger width: no assumption on F, chart columns or mass ratios
is built into the local transport. -/
def LocalLaw (b : Nat) (price : Nat → Int) (A : Nat → Nat → State → Int) :=
  ∀ r j : J b, ∀ s∈layers (min j.val 4), ∀ a : Letter, permit b j.val s a →
    price (arcKey (band b r) (prior b j) (band b j) s (advance s a))=
      after A b r j (advance s a)-before A b r j s

theorem transport_law {k b} (hb : 19≤b) (hk : b≤k) {price A} (law : LocalLaw b price A) :
    LocalLaw k price A := by
  intro r j s hs a pass
  have R := rep_geometry hb hk (j:=r.val) (by omega)
  have C := rep_geometry hb hk (j:=j.val) (by omega)
  let u : J b := ⟨rep k b r,by have := R.1; omega⟩
  let v : J b := ⟨rep k b j,by have := C.1; omega⟩
  have uband : band b u=band k r := R.2.2.2.2.1
  have first := C.2.1; have last := C.2.2.1; have clip := C.2.2.2.1
  have here := C.2.2.2.2.1; have prev := C.2.2.2.2.2
  change v.val=0 ↔ j.val=0 at first
  change v.val=b ↔ j.val=k at last
  change min v.val 4=min j.val 4 at clip
  change band b v=band k j at here
  change prior b v=prior k j at prev
  have same : permit b v.val s a=permit k j.val s a := by
    have f : (v.val==0)=(j.val==0) := Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using first)
    have l : (v.val==b)=(j.val==k) := Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using last)
    simp only [permit,bne, f,l]
  have e := law u v s (clip ▸ hs) a (same ▸ pass)
  rw [uband,prev,here] at e
  have aft : after A b u v (advance s a)=after A k r j (advance s a) := by simp only [after,last,uband,here]
  have bef : before A b u v s=before A k r j s := by
    by_cases f : j.val=0
    · simp [before,f,first.mpr f]
    · have n := mt first.mp f
      simp [prior,f,n] at prev
      simp only [before,if_neg f,if_neg n,uband,prev]
  rwa [aft,bef] at e

theorem physical_line_zero {b k} (hb : 19≤b) (hk : b≤k) {price A}
    (law : LocalLaw b price A) (F : Finset (Site k))
    (np : ∀ g r, ¬Pitch (view F g) (teeth k r)) :
    ∑ p : Fin 8 × J k × J k, price (line F p.1 p.2.1 p.2.2)=0 := by
  have larger := transport_law hb hk law
  have one (g : Fin 8) (r : J k) : ∑ j : J k, price (line F g r j)=0 := by
    let s (n : Nat) := prefixState (view F g) (teeth k r) n
    let f (n : Nat) := if n=k+1 then 0 else before A k r n (s n)
    have eq (j : J k) : price (line F g r j)=f (j.val+1)-f j.val := by
      obtain ⟨hs,p⟩ := physical_step _ _ (np g r) j
      have h := larger r j _ hs _ p
      have prev : 3*j.val-3=3*(j.val-1) := by omega
      change price (arcKey _ (if j.val=0 then 0 else axis (N k) 8 (3*j.val-3)+1) _ _ _)=_
      rw [prev]
      change price (arcKey (band k r) (prior k j) (band k j) _ _)=_
      change price (arcKey (band k r) (prior k j) (band k j) (s j) (advance (s j) (letter _ _ j)))=_
      rw [show price (arcKey (band k r) (prior k j) (band k j) (s j) (advance (s j) (letter _ _ j)))=_ from h]
      have := j.isLt
      by_cases l : j.val=k <;> simp [f,after,before,s,l,show j.val≠k+1 by omega,prefixState]
    simp only [eq]
    rw [Fin.sum_univ_eq_sum_range (fun n => f (n+1)-f n),sum_range_sub]
    simp [f,before]
  simp only [Fintype.sum_prod_type,one,sum_const_zero]

end GridGraphs.NoPitch.TailRows
