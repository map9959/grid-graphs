import GridGraphs.Geometry.SlitReplay

namespace GridGraphs.Slit.Replay
open Data

def Accept (id : Nat) (w : List Nat) : Prop :=
  langs[id]!.ends (langs[id]!.read 1 w) = true

private theorem empty_rejects (w) : ¬Accept 0 w := by
  have h (q : Nat) : d0.ends q = false := by
    cases q with
    | zero => decide +kernel
    | succ q => cases q with
      | zero => decide +kernel
      | succ q =>
        have len : d0.final.size = 2 := by decide +kernel
        simp [DFA.ends,Array.getElem?_eq_none (by omega : d0.final.size ≤ q+1+1)]
  exact fun e => Bool.noConfusion ((h _).symm.trans e)

private theorem accepts_all {w : List Nat} (hw : ∀ c ∈ w, c<8) : Accept 1 w := by
  change d1.ends (d1.read 1 w) = true
  induction w with
  | nil => decide +kernel
  | cons c cs ih =>
    have less := hw c List.mem_cons_self
    have stay : d1.go 1 c = 1 := by interval_cases c <;> decide
    change d1.ends (d1.read (d1.go 1 c) cs) = true
    rw [stay]; exact ih fun x hx => hw _ (List.mem_cons_of_mem _ hx)

def Valid (w : List Nat) := ∀ c ∈ w, c < 8
private theorem valid_out {L : Local} {q z u v} (tr : Trace L q z u v) : Valid v := by
  induction tr with
  | stop => simp [Valid]
  | @step _ _ e _ _ _ _ _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl|h
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ h

/-- A guarded prefix assembled from actual paired slit words. `c` is a
raw upper bill, and `t` counts retentions exactly (not modulo ten). -/
inductive Prefix : Nat → Nat → Nat → List Nat → Prop
  | guard (w : List Nat) (h : ∀ a ∈ w, a=0) : Prefix 0 0 0 w
  | extend {n t c u z v} (drop : Nat) (hd : drop ≤ 1) :
      Prefix n t c u →
      Trace localTables[(if n=0 then 0 else 2)+drop]! 0 z u v →
      Prefix (n+1) (t+(1-drop)) (c+z) v

theorem Prefix.valid {n t c w} (h : Prefix n t c w) : Valid w := by
  cases h with
  | guard _ h => intro a ha; rw [h a ha]; decide
  | extend _ _ _ tr => exact valid_out tr

theorem Prefix.count_le {n t c w} (h : Prefix n t c w) : t≤n := by
  induction h <;> omega

private theorem phase_lt (t : Nat) : phase t<12 := by unfold phase; split_ifs <;> omega
private theorem phase_le (t : Nat) : phase t≤t := by unfold phase; split_ifs <;> omega

private theorem exists_bucket {n t : Nat} (ht : t≤n) :
    ∃ b, bucket (min n 25) (phase t) = some b := by
  have decid : ∀ n : Fin 26, ∀ s : Fin 12, s.val ≤ n.val →
      (bucket n.val s.val).isSome := by decide
  apply Option.isSome_iff_exists.mp
  apply decid ⟨min n 25,by omega⟩ ⟨phase t,phase_lt t⟩
  change phase t ≤ min n 25
  have := phase_le t; have := phase_lt t; omega

private theorem low_of_accept {n s z w b} (hb : bucket n s = some b)
    (h : Accept (slab n s z) w) : b.1 ≤ z := by
  by_contra! neg
  rcases b with ⟨lb,ids⟩
  simp [slab,hb,show z<lb from neg] at h
  exact empty_rejects _ h

private theorem mem_interval {a b x : Int} (lo : a≤x) (hi : x≤b) : x ∈ interval a b := by
  apply List.mem_map.mpr
  refine ⟨(x-a).toNat,List.mem_range.mpr ?_,?_⟩ <;> omega

private theorem in_requests {old : Nat} (ho : old ≤ 25) {r : Request}
    (hr : r ∈ extension old (min (old+1) 25)) : r ∈ requests := by
  simp only [requests,unique,List.mem_eraseDups,List.mem_append,List.mem_flatMap]
  by_cases last : old=25
  · subst old; exact Or.inl (Or.inr (List.mem_eraseDups.mpr hr))
  · rw [Nat.min_eq_left (by omega)] at hr
    exact Or.inl (Or.inl ⟨_,List.mem_range.mpr (by omega),hr⟩)

private theorem extension_mem {old new s drop lb ids floor os z v}
    (hs : s<12) (hd : drop≤1)
    (hb : bucket old s = some (lb,ids))
    (ho : bucket new (phase (s+(1-drop))) = some (floor,os))
    (hz : floor-1≤z) (h5 : z≤4)
    (hv : lb≤v) (budget : v≤z+norm (s+(1-drop))-norm s)
    (ha : slab old s v ≠ 0) (hD : slab new (phase (s+(1-drop))) z ≠ 1) :
    (⟨slab old s v,(if old=0 then 0 else 2)+drop,slab new (phase (s+(1-drop))) z,
      (z+norm (s+(1-drop))-norm s-v).toNat⟩ : Request) ∈ extension old new := by
  unfold extension
  simp only [List.bind_eq_flatMap,List.mem_flatMap]
  refine ⟨s,List.mem_range.mpr hs,?_⟩
  rw [hb]; simp only [List.mem_flatMap]
  refine ⟨drop,by interval_cases drop <;> simp,?_⟩
  rw [ho]; simp only [List.mem_flatMap]
  refine ⟨z,mem_interval hz h5,v,mem_interval hv budget,?_⟩
  simp [guard,ha,hD]

private theorem widen_bill {L : Local} {q z u v} (h : Trace L q z u v)
    {b : Nat} (hb : z≤b) : Trace L q b u v := by
  induction h generalizing b with
  | stop h1 h2 => exact .stop h1 (by omega)
  | step he hc _ ih => exact .step he (by omega) (ih (by omega))

theorem prefix_bound (ok : replay requests) {n t c w} (h : Prefix n t c w) :
    ∀ z : Int, c ≤ z+norm t → Accept (slab (min n 25) (phase t) z) w := by
  induction h with
  | guard w hw =>
    intro z hz
    have pos : 0≤z := by simpa [norm] using hz
    have eq : slab 0 0 z=2 := by
      change (if z<0 then 0 else 2)=2; simp [not_lt.mpr pos]
    change Accept (slab 0 0 z) w
    rw [eq]
    change d2.ends (d2.read 1 w)=true
    induction w with
    | nil => decide +kernel
    | cons a w ih =>
      have := hw a List.mem_cons_self; subst a
      exact ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
  | @extend n t c u b w drop hd prev tr ih =>
    intro z hz
    let old := min n 25
    let new := min (n+1) 25
    let s := phase t
    let t' := phase (s+(1-drop))
    have ph := phase_step t (1-drop) (by omega)
    change t'=phase (t+(1-drop)) ∧ _ at ph
    change Accept (slab new (phase (t+(1-drop))) z) w
    rw [←ph.1]
    obtain ⟨⟨lb,ids⟩,hin⟩ := exists_bucket prev.count_le
    obtain ⟨⟨floor,os⟩,hout⟩ := exists_bucket (show t+(1-drop)≤n+1 by have := prev.count_le; omega)
    change bucket old s = _ at hin
    rw [←ph.1] at hout
    change bucket new t' = _ at hout
    by_cases high : 5≤z
    · have floor_le : floor ≤ 5 := by
        have test : ∀ i : Fin 26, ∀ j : Fin 12,
            ((bucket i.val j.val).map Prod.fst).getD 0 ≤ 5 := by decide
        have hh := test ⟨new,by dsimp [new]; omega⟩ ⟨t',phase_lt _⟩
        simpa [hout] using hh
      simp only [slab,hout,if_neg (show ¬ z<floor by omega),
        if_neg (show new≠0 by dsimp [new]; omega),if_pos high]
      exact accepts_all (valid_out tr)
    let v : Int := c-norm t
    have src := ih v (by dsimp [v]; omega)
    have ha : slab old s v ≠ 0 := by intro eq; exact empty_rejects u (eq ▸ src)
    let z' := max z (floor-1)
    have fresh : floor ≤ 5 := by
      have test : ∀ i : Fin 26, ∀ j : Fin 12,
          ((bucket i.val j.val).map Prod.fst).getD 0 ≤ 5 := by decide
      have hh := test ⟨new,by dsimp [new]; omega⟩ ⟨t',phase_lt _⟩
      simpa [hout] using hh
    have fee : (b : Int) ≤ z'+norm (s+(1-drop))-norm s-v := by
      dsimp [z',v,s]; push_cast at hz; omega
    have stepOk : Accept (slab new t' z') w := by
      by_cases univ : slab new t' z'=1
      · rw [univ]; exact accepts_all (valid_out tr)
      have hr := extension_mem (phase_lt t) hd hin hout (le_max_right ..)
        (show z'≤4 by dsimp [z']; omega) (low_of_accept hin src) (by omega) ha univ
      have eq : new=min (old+1) 25 := by dsimp [new,old]; omega
      rw [eq] at hr
      have hr' := in_requests (by dsimp [old]; omega) hr
      have mask : (if old=0 then 0 else 2)=(if n=0 then 0 else 2) := by
        dsimp [old]; split_ifs <;> omega
      let loc := (if old=0 then 0 else 2)+drop
      have hloc : loc ≠ 4 := by dsimp [loc]; split_ifs <;> omega
      have tr' : Trace localTables[loc]! 0 (z'+norm (s+(1-drop))-norm s-v).toNat u w := by
        dsimp [loc]; rw [mask]; exact widen_bill tr (by omega)
      rw [← eq] at hr'
      have image := replay_sound ok hr' tr' src
      simpa [Request.job,Accept,hloc,loc] using image
    have := low_of_accept hout stepOk
    have eq : z'=z := by dsimp [z'] at *; omega
    rwa [←eq]

private theorem inter_mem {n i j lb ids rb os z} (hn : 4≤n) (hN : n≤25)
    (hi : i≤2) (hj : j≤n) (pos : 0 < i+j)
    (h₁ : bucket 2 (phase i) = some (lb,ids)) (h₂ : bucket n (phase j) = some (rb,os))
    (lo : lb≤z) (high : z ≤ maxBill (i+j)-norm i-norm j-rb) :
    (⟨slab 2 (phase i) z,4,slab n (phase j) (maxBill (i+j)-norm i-norm j-z),0⟩ :
      Request) ∈ requests := by
  simp only [requests,unique,List.mem_eraseDups,List.mem_append]
  right; apply List.mem_flatMap.mpr
  refine ⟨n-4,List.mem_range.mpr (by omega),?_⟩
  rw [show 4+(n-4)=n by omega]
  unfold intersections
  simp only [List.bind_eq_flatMap,List.mem_flatMap]
  refine ⟨i,List.mem_range.mpr (by omega),j,List.mem_range.mpr (by omega),?_⟩
  simp only [guard,if_pos pos,List.pure_def,h₁,h₂,List.mem_flatMap,List.mem_singleton]
  exact ⟨⟨⟩,trivial,z,mem_interval lo high,rfl⟩

/-- The split is two guarded triples and an arbitrary suffix of at least
four triples. The matching trace reverses each slit letter, not the word.
Bills use the same two budgets as the normalized interval computation. -/
theorem cap_excludes (ok : replay requests) {n i j c d u v} (hn : 4≤n) (pos : 0 < i+j)
    (l : Prefix 2 i c u) (r : Prefix n j d v) (matched : Trace reflect 0 0 u v) :
    maxBill (i+j) < (c : Int)+d := by
  by_contra! bad
  let N := min n 25
  let J := if n≤25 then j else phase j
  have small : i≤2 := l.count_le
  have pj : phase J=phase j := by dsimp [J]; split_ifs <;> unfold phase <;> split_ifs <;> omega
  have okJ : J≤N := by dsimp [J,N]; have := r.count_le; have := phase_lt j; split_ifs <;> omega
  have jpos : 0 < i+J := by dsimp [J,phase]; split_ifs <;> omega
  have capEq : maxBill (i+J)-norm i-norm J=maxBill (i+j)-norm i-norm j := by
    dsimp [J]; split_ifs
    · rfl
    · exact paired_phase _ _
  let z : Int := c-norm i
  let y := maxBill (i+J)-norm i-norm J-z
  have hl : Accept (slab 2 (phase i) z) u := prefix_bound ok l z (by dsimp [z]; omega)
  have hr : Accept (slab N (phase J) y) v := by
    rw [pj]; apply prefix_bound ok r y
    dsimp [y,z]; rw [capEq]; omega
  obtain ⟨⟨lb,ids⟩,hb⟩ := exists_bucket l.count_le
  change bucket 2 (phase i)=_ at hb
  obtain ⟨⟨rb,os⟩,ho⟩ := exists_bucket r.count_le
  change bucket N (phase j)=_ at ho
  rw [←pj] at ho
  have low := low_of_accept hb hl
  have high := low_of_accept ho hr
  have req := inter_mem (n := N) (by dsimp [N]; omega) (by dsimp [N]; omega)
    small okJ jpos hb ho low (by dsimp [y] at high; omega)
  have fail := replay_sound ok req matched hl
  change ((langs[slab N (phase J) y]!.ends ((langs[slab N (phase J) y]!).read 1 v))
    != true) = true at fail
  rw [show (langs[slab N (phase J) y]!.ends ((langs[slab N (phase J) y]!).read 1 v)) =
      true from hr] at fail
  exact Bool.noConfusion fail

end GridGraphs.Slit.Replay
