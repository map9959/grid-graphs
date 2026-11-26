import GridGraphs.ResidueTwoUpper.OneGap.FanSeedData

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
open L7

-- 0: before chosen isolate, 1: past it, 2: past another aligned tile,
-- 3: witnessed a forbidden seed or suffix. Each state can also wait.
def event (j m : Nat) := decide (4≤j ∧ j≤28 ∧ j%3=1 ∧ m &&& 186=0)
def jump (j a b c t : Nat) :=
  let m := window a b c 1
  let k := window a b c 4
  if t=0 && event j m then (if m=64 then 1 else 3)
  else if (t=1 || t=2) && j%3==1 then
    (if m=72 && lane k 0==1 && (t != 2 || lane k 3==1) then 2 else 3)
  else t
private def start (s f : Bool) : List State := (opt s f 0).flatMap fun a =>
  (opt s f 1).map fun b => (a,b,0)
private def go (s f : Bool) (j : Nat) (v : State) : List State :=
  ((opt s f (j+2)).filter (cleanBand j v.1 v.2.1)).flatMap fun c =>
    [(v.2.1,c,v.2.2),(v.2.1,c,jump j v.1 v.2.1 c v.2.2)]
private def live (s f : Bool) : Nat → List State
  | 0 => start s f
  | j+1 => ((live s f j).flatMap (go s f j)).eraseDups
private theorem verified : ∀ s f : Bool,
    (live s f 24).all (live s f 21).contains && (live s f 33).all (fun v => v.2.2!=3) := by native_decide

theorem suffix (u : Nat) (s f : Bool) (X : Nat → Nat) (lt : ∀ j, X j<128)
    (fr : ∀ j<35+42*u, columnOK (35+42*u) s f j (X j))
    (bands : ∀ j<33+42*u, cleanBand (fold u j) (X j) (X (j+1)) (X (j+2)))
    (i : Nat) (hi : 4≤ i ∧ i+5≤33+42*u ∧ i%3=1)
    (iso : window (X i) (X (i+1)) (X (i+2)) 1 &&& 186=0) :
    window (X i) (X (i+1)) (X (i+2)) 1=64 ∧
    ∀ j, i<j → j<33+42*u → j%3=1 →
      window (X j) (X (j+1)) (X (j+2)) 1=72 ∧
      lane (window (X j) (X (j+1)) (X (j+2)) 4) 0=1 ∧
      (i+3<j → lane (window (X j) (X (j+1)) (X (j+2)) 4) 3=1) := by
  have cert : ((live s f 24).all (live s f 21).contains=true) ∧
      (live s f 33).all (fun v => v.2.2!=3)=true := by simpa using verified s f
  let R (j t : Nat) := (X j,X (j+1),t)∈live s f (fold u j)
  let J (j t : Nat) := jump (fold u j) (X j) (X (j+1)) (X (j+2)) t
  have col (j t : Nat) (hj : j<33+42*u) (ht : t≤2) : X (j+t)∈opt s f (fold u j+t) := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (lt _),?_⟩
    have eq (r : Nat) : preset (35+42*u) s f r (j+t)=preset 35 s f r (fold u j+t) := by
      unfold preset fold; split_ifs <;> first | rfl | omega
    simpa only [columnOK,eq] using fr (j+t) (by omega)
  have init : R 0 0 := by
    apply List.mem_flatMap.mpr; exact ⟨_,col 0 0 (by omega) (by decide),
      List.mem_map.mpr ⟨_,col 0 1 (by omega) (by decide),rfl⟩⟩
  have advance {j t q : Nat} (hj : j<33+42*u) (in' : R j t) (next : q=t ∨ q=J j t) : R (j+1) q := by
    have h : (X (j+1),X (j+2),q)∈live s f (fold u j+1) := by
      rw [live,List.mem_eraseDups,List.mem_flatMap]; refine ⟨_,in',List.mem_flatMap.mpr ?_⟩
      exact ⟨_,List.mem_filter.mpr ⟨col j 2 hj (by decide),bands j hj⟩, by rcases next with rfl|rfl <;> simp [J]⟩
    dsimp only [R]; rcases fold_step u j with eq|⟨a,b⟩
    · rwa [eq]
    · rw [a] at h; rw [b]; exact List.contains_iff_mem.mp (List.all_eq_true.mp cert.1 _ h)
  have wait {j k t : Nat} (jk : j≤k) (hk : k≤33+42*u) (h : R j t) : R k t := by
    induction k,jk using Nat.le_induction with
    | base => exact h
    | succ k _ ih => exact advance (by omega) (ih (by omega)) (.inl rfl)
  have safe {j t : Nat} (hj : j≤33+42*u) (h : R j t) : t≠3 := by
    have done := wait hj le_rfl h
    dsimp only [R] at done; rw [show fold u (33+42*u)=33 by unfold fold; split_ifs <;> omega] at done
    simpa using List.all_eq_true.mp cert.2 _ done
  have phase (j : Nat) : fold u j%3=j%3 := by unfold fold; split_ifs <;> omega
  have event' : event (fold u i) (window (X i) (X (i+1)) (X (i+2)) 1) := by
    simp only [event,decide_eq_true_eq]; refine ⟨?_,?_,(phase i).trans hi.2.2,iso⟩ <;>
      unfold fold <;> split_ifs <;> omega
  have after := advance (by omega : i<33+42*u) (wait (by omega : 0≤ i) (by omega) init) (.inr (rfl : J i 0=_))
  have seed : window (X i) (X (i+1)) (X (i+2)) 1=64 := by
    by_contra h; exact safe (by omega) after (by simp [J,jump,event',h])
  have one : R (i+1) 1 := by
    have ev := event'; rw [seed] at ev
    simpa [J,jump,ev,seed] using after
  have step {j t : Nat} (hj : j<33+42*u) (aligned : j%3=1) (active : t=1 ∨ t=2) (h : R j t) :
      R (j+1) 2 ∧ window (X j) (X (j+1)) (X (j+2)) 1=72 ∧
      lane (window (X j) (X (j+1)) (X (j+2)) 4) 0=1 ∧
      (t=2 → lane (window (X j) (X (j+1)) (X (j+2)) 4) 3=1) := by
    have H := advance hj h (.inr (rfl : J j t=_)); have G := safe (by omega) H
    rcases active with rfl|rfl <;> simp [J,jump,phase,aligned] at G H <;> split_ifs at G H <;> simp_all
  refine ⟨seed,?_⟩; intro j hj lim aligned
  obtain ⟨_,a,b,_⟩ := step lim aligned (.inl rfl) (wait (by omega) (by omega) one)
  refine ⟨a,b,fun late => ?_⟩
  have first := (step (by omega : i+3<33+42*u) (by omega) (.inl rfl) (wait (by omega) (by omega) one)).1
  exact (step lim aligned (.inr rfl) (wait (by omega) (by omega) first)).2.2.2 rfl

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanSeed
