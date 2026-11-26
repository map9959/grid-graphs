import GridGraphs.ResidueTwoUpper.OneGap.RootedEastContact

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.FiniteTransfer

private abbrev Key := Nat × Nat × Bool × Nat × Nat
private abbrev Val := Nat × Nat
private def text := include_str "CrampedTransfer.txt"
private def nums (s : String) := (s.splitOn " ").filterMap String.toNat?
private def halves := text.splitOn "\n#\n"
private def pool := ((halves.headD "").splitOn "\n").toArray.map (Std.HashSet.ofList ∘ nums)
private def values (i : Nat) := pool[i]?.getD ∅
private def parse (line : String) : Option (Key × Val) :=
  match nums line with
  | [s,e,t,n,w,b,r] => some ((s,e,t==1,n,w),(b,r))
  | _ => none
private def entries := ((halves[1]?.getD "").splitOn "\n").filterMap parse
private def table := Std.HashMap.ofList entries
private def code (a b : Nat) := 1024*a+b
private def north (v : Word) := code v.1 v.2.1
private def west (v : Word) := code v.1 v.2.2.1
private def south (v : Word) := code v.2.2.1 v.2.2.2
private def east (v : Word) := code v.2.1 v.2.2.2
private def allows (id x : Nat) := id==0 || (values id).contains x
private def verified : Bool :=
  table.toList.all fun ((s,e,t,n,w),b,r) =>
    (rimBank (12-s) (12-e) t (s==0)).all fun v =>
      !(allows n (north v) && allows w (west v)) ||
        (allows b (south v) && allows r (east v))
private theorem check_table : verified=true := by native_decide

-- Unknown transitions return the unconstrained pair (0,0).
private def move (s e : Nat) (top : Bool) (n w : Nat) : Val :=
  table.getD (s,e,top,n,w) (0,0)

private theorem move_ok (s e : Nat) (top : Bool) (n w : Nat) (v : Word)
    (mem : v∈rimBank (12-s) (12-e) top (s==0))
    (N : allows n (north v)) (W : allows w (west v)) :
    allows (move s e top n w).1 (south v) ∧ allows (move s e top n w).2 (east v) := by
  let k : Key := (s,e,top,n,w)
  unfold move
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases h : table[k]? with
  | none => exact ⟨rfl,rfl⟩
  | some p =>
    simp only [Option.getD_some]
    have elem : (k,p)∈table.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
    have ck := List.all_eq_true.mp (List.all_eq_true.mp check_table _ elem) _ mem
    simpa only [k,N,W,Bool.true_and,Bool.not_true,Bool.false_or,Bool.and_eq_true] using ck

private def dist (n i : Nat) := min 6 (n-2-i)
private def step (h w r : Nat) (above : Array Val) (a : Array Val) (c : Nat) :=
  a.push (move (dist h r) (dist w c) (r==0) (above[c]?.getD (0,0)).1 (a.back?.getD (0,0)).2)
private def row (h w r : Nat) (above : Array Val) (len : Nat) :=
  (List.range len).foldl (step h w r above) #[]
private def scan (h w rows : Nat) :=
  (List.range rows).foldl (fun above r => row h w r above (w-1)) #[]

private def RowOK (a : Array Val) (T : Tiles) (r cols : Nat) : Prop :=
  a.size=cols ∧ ∀ c<cols, ∃ z, a[c]?=some z ∧ allows z.1 (south (word T r c)) ∧ allows z.2 (east (word T r c))

private theorem row_ok (h w r len : Nat) (T : Tiles) (above : Array Val)
    (mem : ∀ c<len, word T r c∈rimBank (12-dist h r) (12-dist w c) (r==0) (dist h r==0))
    (n : ∀ c<len, allows (above[c]?.getD (0,0)).1 (north (word T r c))) :
    RowOK (row h w r above len) T r len := by
  induction len with
  | zero => exact ⟨rfl,by omega⟩
  | succ c ih =>
    let a := row h w r above c
    have old : RowOK a T r c := ih (fun _ hc => mem _ (by omega)) (fun _ hc => n _ (by omega))
    have left : allows (a.back?.getD (0,0)).2 (west (word T r c)) := by
      cases c with
      | zero =>
        rw [Array.size_eq_zero_iff.mp old.1]; rfl
      | succ i =>
        obtain ⟨z,hit,_,ok⟩ := old.2 i (by omega)
        rw [Array.back?_eq_getElem?,old.1]
        simp only [Nat.add_sub_cancel,hit,Option.getD_some]
        exact ok
    let z := move (dist h r) (dist w c) (r==0) (above[c]?.getD (0,0)).1 (a.back?.getD (0,0)).2
    have ok := move_ok _ _ _ _ _ _ (mem c (by omega)) (n c (by omega)) left
    rw [show row h w r above (c+1)=a.push z by simp [row,List.range_succ,a,z,step]]
    refine ⟨by simp [old.1],?_⟩
    intro i hi
    rw [Array.getElem?_push,old.1]
    by_cases same : i=c
    · subst i; exact ⟨z,by simp,ok⟩
    · simpa only [if_neg same] using old.2 i (by omega)

def rejects (h w : Nat) : Bool :=
  let id := ((scan h w (h-1)).back?.getD (0,0)).2
  id != 0 && (values id).isEmpty

theorem sound (h w : Nat) (hl : 2≤h) (wl : 2≤w) (T : Tiles)
    (mem : ∀ r c : Nat, r+2≤h → c+2≤w →
      word T r c∈rimBank (endTag h r) (endTag w c) (r==0) (r+2==h)) : rejects h w=false := by
  have tag (n i : Nat) (fit : i+2≤n) : endTag n i=12-dist n i := by
    unfold endTag dist; split <;> omega
  have rowMem (r c : Nat) (hr : r+2≤h) (hc : c+2≤w) := mem r c hr hc
  have ok (r : Nat) (hr : r+2≤h) : RowOK (scan h w (r+1)) T r (w-1) := by
    induction r with
    | zero =>
      apply row_ok  _ _ 0 _ _ #[]
      · intro c hc
        have s : (dist h 0==0)=(0+2==h) := by apply Bool.eq_iff_iff.mpr; simp [dist]; omega
        simpa only [tag h 0 hr,tag w c (by omega),s] using rowMem 0 c hr (by omega)
      · intros; rfl
    | succ i ih =>
      have prev := ih (by omega)
      rw [show scan h w (i+1+1)=row h w (i+1) (scan h w (i+1)) (w-1) by simp [scan,List.range_succ (n:=i+1)]]
      apply row_ok
      · intro c hc
        have s : (dist h (i+1)==0)=(i+1+2==h) := by apply Bool.eq_iff_iff.mpr; simp [dist]; omega
        simpa only [tag h (i+1) hr,tag w c (by omega),s] using rowMem (i+1) c hr (by omega)
      · intro c hc
        obtain ⟨z,hit,ok',_⟩ := prev.2 c hc
        rw [hit]; exact ok'
  have last := ok (h-2) (by omega)
  rw [show h-2+1=h-1 by omega] at last
  obtain ⟨z,hit,_,edge⟩ := last.2 (w-2) (by omega)
  simp only [rejects,Array.back?_eq_getElem?,last.1,show w-1-1=w-2 by omega,hit,Option.getD_some]
  by_cases zero : z.2=0
  · simp [zero]
  · have yes : (values z.2).contains (east (word T (h-2) (w-2)))=true := by simpa [allows,zero] using edge
    have ne := Std.HashSet.isEmpty_eq_false_iff_exists_mem.mpr ⟨_,Std.HashSet.contains_iff_mem.mp yes⟩
    simp [ne]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted.FiniteTransfer
