import GridGraphs.NoPitch.Budget.DecodedPaths19

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset Keys GridGraphs.NoPitch.Dual
variable {k : Nat}

private theorem run_amount (F : Finset (Site k)) (v : Fin (N k)) {a len n : Nat}
    (width : a+len=k+1) (h : run (prefixState F v a) ((List.range' a len).map (letter F v))=some n) :
    n=∑ j : Fin len, debit (prefixState F v (a+j.val)) (letter F v (a+j.val)) (a+j.val==k) := by
  induction len generalizing a n with
  | zero => simpa [run] using h.symm
  | succ len ih =>
    rw [List.range'_succ,List.map_cons,run] at h
    simp only [Option.bind_apply,Option.bind_eq_some_iff,Option.pure_apply,Option.some.injEq] at h
    obtain ⟨_,_,b,tail,rfl⟩ := h
    have eq := ih (a:=a+1) (n:=b) (by omega) tail
    have flag : ((List.range' (a+1) len).map (letter F v)).isEmpty=(a==k) := by
      cases len <;> simp [List.range'_succ] <;> omega
    rw [eq,flag,Fin.sum_univ_succ]; simp [Nat.add_comm,Nat.add_left_comm]

theorem axisDebit_steps (F : Finset (Site k)) (np : ∀ r, ¬Pitch F (teeth k r)) :
    axisDebit F=∑ r : J k, ∑ j : J k,
      (debit (prefixState F (teeth k r) j.val) (letter F (teeth k r) j.val) (j.val==k):Int) := by
  apply sum_congr rfl; intro r _
  obtain ⟨n,run,_⟩ := physical_line F _ (np r)
  rw [run]; simp only [Option.getD_some,←Nat.cast_sum]
  apply congrArg Nat.cast
  have z := run_amount F (teeth k r) (a:=0) (len:=k+1) (n:=n) (by omega) (by
    simpa only [word,List.range_eq_range',prefixState] using run)
  simpa only [Nat.zero_add] using z

/-- Pull a charge back from the actual packed transition key. The
previous and next states occupy the last two base-90 digits. -/
def unstate (n : Nat) : State :=
  let m := n/18
  let p := n/2%9
  ⟨if m=0 then .pre else if m=1 then .on else if m=2 then .gap else if m=3 then .p0 else .p1,
    if p=0 then none else some ⟨(p-1).testBit 2,(p-1).testBit 1,(p-1).testBit 0⟩,
    n%2==1⟩
private theorem state_ok : ∀ s : State, unstate (state s)=s ∧ state s<90 := by decide +kernel
def debitKey (k key : Nat) :=
  let n := key/8
  let prev := unstate (n/90%90)
  let next := unstate (n%90)
  debit prev (next.prev.getD default) (n/8100%32==axis (N k) 8 (3*k))

private theorem end_axis (i : J k) (hk : 6≤k) :
    (axis (N k) 8 (3*i.val)==axis (N k) 8 (3*k))=(i.val==k) := by
  apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq,axis,N]
  split_ifs <;> have := i.isLt <;> omega

theorem debitKey_physical (F : Finset (Site k)) (hk : 6≤k) (g : Fin 8) (i j : J k) :
    debitKey k (line F g i j)=debit (prefixState (view F g) (teeth k i) j.val)
      (letter (view F g) (teeth k i) j.val) (j.val==k) := by
  let v := teeth k i
  let S := view F g
  let s := prefixState S v j.val
  let t := prefixState S v (j.val+1)
  let y := axis (N k) 8 (3*j.val)
  let x := pack [axis (N k) 8 v.val,if j.val=0 then 0 else axis (N k) 8 (3*j.val-3)+1]
  let n := ((32*x+y)*90+state s)*90+state t
  change debit (unstate ((8*n+3)/8/90%90)) ((unstate ((8*n+3)/8%90)).prev.getD default)
    ((8*n+3)/8/8100%32==axis (N k) 8 (3*k))=_
  have a := state_ok s; have b := state_ok t
  have bound : y<32 := by unfold y axis; split_ifs <;> unfold N at * <;> have := j.isLt <;> omega
  have deq : (8*n+3)/8=n := by omega
  rw [deq,show n/90%90=state s by dsimp only [n]; omega,
    show n%90=state t by dsimp only [n]; omega,show n/8100%32=y by dsimp only [n]; omega,
    a.1,b.1,end_axis j hk]
  rfl

theorem eightfold_key_debit (F : Finset (Site k)) (hk : 6≤k)
    (np : ∀ g r, ¬Pitch (view F g) (teeth k r)) :
    ∑ p : Fin 8 × J k × J k, (debitKey k (line F p.1 p.2.1 p.2.2):Int) =
      ∑ g : Fin 8, axisDebit (view F g) := by
  simp only [Fintype.sum_prod_type,debitKey_physical F hk,axisDebit_steps _ (np _)]

end GridGraphs.NoPitch.Budget
