import GridGraphs.ResidueTwoUpper.OneGap.RootCoverField

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted

private def key (a b : Nat) := a+1024*b
private def nKey (w : Word) := key w.1 w.2.1
private def sKey (w : Word) := key w.2.2.1 w.2.2.2
private def wKey (w : Word) := key w.1 w.2.2.1
private def eKey (w : Word) := key w.2.1 w.2.2.2

private abbrev Keys := Std.HashSet Nat
private structure Out where
  below : Keys
  right : Keys
private def output (ws : List Word) : Out :=
  ⟨Std.HashSet.ofList (ws.map sKey), Std.HashSet.ofList (ws.map eKey)⟩
private def keep (above left : Option Out) (w : Word) :=
  above.all (fun a => a.below.contains (nKey w)) &&
  left.all (fun a => a.right.contains (wKey w))
private def advance (ws : List Word) (above left : Option Out) :=
  output (ws.filter (keep above left))

private def project (width : Nat) (ws : Nat → List Word) (above : Array Out) :
    Array Out :=
  (List.range width).foldl (fun a c => a.push (advance (ws c) above[c]? a.back?)) #[]

private def scan (height width : Nat) (D : Nat → Nat → List Word) : Array Out :=
  (List.range height).foldl (fun a r => project width (D r) a) #[]

private def OutputAt (a : Out) (w : Word) : Prop := sKey w∈a.below ∧ eKey w∈a.right
private theorem advance_sound {ws : List Word} {n l : Option Out} {w : Word}
    (mem : w∈ws) (nOK : ∀ a∈n, nKey w∈a.below) (lOK : ∀ a∈l, wKey w∈a.right) :
    OutputAt (advance ws n l) w := by
  have ok : keep n l w=true := by
    cases n <;> cases l <;> simp_all [keep,Std.HashSet.contains_iff_mem]
  have m := List.mem_filter.mpr ⟨mem,ok⟩
  constructor <;> simp only [advance,output,Std.HashSet.mem_ofList,List.contains_iff_mem] <;>
    exact List.mem_map.mpr ⟨_,m,rfl⟩

private def RowOK (a : Array Out) (t : Tiles) (r cols : Nat) : Prop :=
  a.size=cols ∧ ∀ c<cols, ∃ z, a[c]?=some z ∧ OutputAt z (word t r c)

private theorem project_ok {t : Tiles} (r width : Nat) (ws : Nat → List Word) (above : Array Out)
    (mem : ∀ c<width, word t r c∈ws c)
    (north : ∀ c<width, ∀ z∈above[c]?, nKey (word t r c)∈z.below) :
    RowOK (project width ws above) t r width := by
  induction width with
  | zero => exact ⟨rfl,by omega⟩
  | succ c ih =>
    let a := project c ws above
    have old : RowOK a t r c := ih (fun i hi => mem i (by omega)) (fun i hi => north i (by omega))
    have left : ∀ z∈a.back?, wKey (word t r c)∈z.right := by
      intro z hz
      cases c with
      | zero =>
        have nil : a=#[] := Array.size_eq_zero_iff.mp old.1
        simp [nil] at hz
      | succ i =>
        obtain ⟨b,atB,_,edge⟩ := old.2 i (by omega)
        rw [Array.back?_eq_getElem?,old.1] at hz
        simp only [Nat.add_sub_cancel,atB,Option.mem_some_iff] at hz
        subst z; exact edge
    let z := advance (ws c) above[c]? a.back?
    have oz : OutputAt z (word t r c) := advance_sound (mem c (by omega)) (north c (by omega)) left
    have eq : project (c+1) ws above=a.push z := by simp [project,List.range_succ,a,z]
    rw [eq]
    refine ⟨by simp [old.1],?_⟩
    intro i hi
    rw [Array.getElem?_push,old.1]
    by_cases e : i=c
    · subst i; exact ⟨_,by simp,oz⟩
    · simpa only [if_neg e] using old.2 i (by omega)

private theorem scan_ok (h w : Nat) (D : Nat → Nat → List Word) (t : Tiles)
    (mem : ∀ r<h+1, ∀ c<w, word t r c∈D r c) :
    RowOK (scan (h+1) w D) t h w := by
  induction h with
  | zero =>
    apply project_ok 0 w _ #[] (mem 0 (by decide))
    simp
  | succ h ih =>
    have prev := ih (fun r hr c hc => mem r (by omega) c hc)
    have eq : scan (h+1+1) w D=project w (D (h+1)) (scan (h+1) w D) := by
      simp [scan,List.range_succ (n:=h+1)]
    rw [eq]
    apply project_ok _ _ _ _ (mem _ (by omega))
    intro c hc z hz
    obtain ⟨a,atA,edge,_⟩ := prev.2 c hc
    rw [atA] at hz
    exact (Option.mem_some_iff.mp hz) ▸ edge

/-- Bank lookup is shared for the whole rectangle. No array of
physical-board-sized assignments is required. -/
@[noinline] private def tables :=
  Array.ofFn fun a : Fin 7 => Array.ofFn fun b : Fin 7 =>
    (labelBank (6+a.val) (6+b.val) false (a.val==6),
     labelBank (6+a.val) (6+b.val) true (a.val==6))

private def cellBank (h w r c : Nat) :=
  let a := endTag h r-6
  let b := endTag w c-6
  let pair := ((tables[a]?).bind (fun row => row[b]?)).getD ([],[])
  if r=0 then pair.2 else pair.1

private theorem cellBank_eq (h w r c : Nat) (hr : r+2≤h) (hc : c+2≤w) :
    cellBank h w r c=labelBank (endTag h r) (endTag w c) (r==0) (r+2==h) := by
  have rr := tag_range hr
  have cc := tag_range hc
  have x : endTag h r-6<7 := by omega
  have y : endTag w c-6<7 := by omega
  have e : (endTag h r-6==6)=(r+2==h) := by
    apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq,endTag]; split_ifs <;> norm_num <;> omega
  simp only [cellBank,tables,Array.getElem?_ofFn,dif_pos x,dif_pos y,Option.bind_some,
    Option.getD_some,e,show 6+(endTag h r-6)=endTag h r by omega,
    show 6+(endTag w c-6)=endTag w c by omega]
  split
  · rename_i z; subst r; rfl
  · rename_i nz; rw [beq_eq_false_iff_ne.mpr nz]

def southReject (h w : Nat) : Bool :=
  (scan (h-1) (w-1) (cellBank h w)).back?.any (fun o => o.below.isEmpty)

theorem southReject_sound {h w : Nat} (hl : 2≤h) (wl : 2≤w)
    (t : Tiles) (mem : ∀ r c : Nat, r+2≤h → c+2≤w →
      word t r c∈labelBank (endTag h r) (endTag w c) (r==0) (r+2==h)) :
    southReject h w=false := by
  have ok := scan_ok (h-2) (w-1) (cellBank h w) t (by
    intro r hr c hc
    rw [cellBank_eq _ _ _ _ (by omega) (by omega)]
    exact mem r c (by omega) (by omega))
  rw [show h-2+1=h-1 by omega] at ok
  obtain ⟨z,atZ,bel,_⟩ := ok.2 (w-2) (by omega)
  simp only [southReject,Array.back?_eq_getElem?,ok.1,show w-1-1=w-2 by omega,atZ,Option.any_some]
  exact Std.HashSet.isEmpty_eq_false_iff_exists_mem.mpr ⟨_,bel⟩

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan.Rooted
