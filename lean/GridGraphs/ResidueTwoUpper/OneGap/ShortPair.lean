import GridGraphs.ResidueTwoUpper.OneGap.ShortBoard

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short

/-- Lift two overlapping sites to one strip state. Both edge-owner
comparisons survive at a transverse crossing of the paired strip. -/
abbrev Duo := Label × Label
abbrev Sheet := Array (Array (List Duo))
def getPair (G : Sheet) (r c : Nat) := ((G[r]?.getD #[])[c]?).getD []
def mkSheet (h w : Nat) (f : Nat → Nat → List Duo) : Sheet :=
  Array.ofFn fun i : Fin h => Array.ofFn fun j : Fin w => f i j
def bonds (A B : List Label) (d : Nat) : List Duo := A.flatMap fun a =>
  (B.filter fun b => port true d a==port false (d+2) b).map (a,·)

def firstPair (s : Nat) (v : Bool) (G : Board) :=
  mkSheet (s-v.toNat) (s-(!v).toNat) fun r c =>
    bonds (atRC G r c) (atRC G (r+v.toNat) (c+(!v).toNat)) v.toNat
def duoCode (v : Bool) (send : Bool) (d : Nat) (z : Duo) :=
  if d%2=v.toNat then
    let a := if d<2 then z.2 else z.1
    5*a.1+a.2
  else 2048*port send d z.1+port send d z.2
def narrow (v : Bool) (d : Nat) (src dst : List Duo) :=
  let keys := Std.HashSet.ofList (src.map (duoCode v true d))
  dst.filter fun b => keys.contains (duoCode v false ((d+2)%4) b)
def neighbor (r c d : Nat) := match d with
  | 0 => (r,c+1) | 1 => (r+1,c) | 2 => (r,c-1) | _ => (r-1,c)
def available (h w r c d : Nat) := match d with
  | 0 => c+1<w | 1 => r+1<h | 2 => 0<c | _ => 0<r
instance (h w r c d) : Decidable (available h w r c d) := by unfold available; split <;> infer_instance
def pstep (h w : Nat) (v : Bool) (d : Nat) (G : Sheet) (r c : Nat) : Sheet :=
  let x := if d<2 then r else h-1-r
  let y := if d<2 then c else w-1-c
  let e := (d+2)%4
  if available h w x y e then
    let z := neighbor x y e
    G.setIfInBounds x ((G[x]?.getD #[]).setIfInBounds y (narrow v d (getPair G z.1 z.2) (getPair G x y)))
  else G
def ppass (h w : Nat) (v : Bool) (d : Nat) (G : Sheet) :=
  (List.range h).foldl (fun A r => (List.range w).foldl (fun B c => pstep h w v d B r c) A) G
def tighten (h w : Nat) (v : Bool) : Nat → Sheet → Sheet
  | 0,G => G
  | k+1,G =>
    let next := (List.range 4).foldl (fun A d => ppass h w v d A) G
    if G==next then next else tighten h w v k next
def dropPair (s : Nat) (v : Bool) (G : Sheet) (A : Board) : Board := build s fun r c =>
  let dr := v.toNat; let dc := (!v).toNat
  let fore := Std.HashSet.ofList ((getPair G r c).map Prod.fst)
  let back := Std.HashSet.ofList ((getPair G (r-dr) (c-dc)).map Prod.snd)
  (atRC A r c).filter fun z =>
    (!(r+dr<s && c+dc<s) || fore.contains z) && (!(dr≤r && dc≤c) || back.contains z)
def pairSweep (s : Nat) (v : Bool) (fuel : Nat) (A : Board) :=
  dropPair s v (tighten (s-v.toNat) (s-(!v).toNat) v fuel (firstPair s v A)) A

private def Fits (h w : Nat) (M : Nat → Nat → Duo) (A : Sheet) :=
  ∀ r<h, ∀ c<w, M r c∈getPair A r c
private def DAgree (s : Nat) (v : Bool) (M : Nat → Nat → Duo) :=
  let h := s-v.toNat; let w := s-(!v).toNat
  ∀ r<h, ∀ c<w, ∀ d : Fin 4, let e := (d.val+2)%4
    available h w r c e → let z := neighbor r c e
    duoCode v true d (M z.1 z.2)=duoCode v false e (M r c)

private theorem lift_agree {s M} (m : Agree s M) (v : Bool) :
    DAgree s v (fun r c => (M r c,M (r+v.toNat) (c+(!v).toNat))) := by
  unfold DAgree
  dsimp only
  intro r hr c hc d ae
  have horiz (r c) (hr : r<s) (hc : c+1<s) := (m r hr c (by omega)).1 hc
  have vert (r c) (hr : r+1<s) (hc : c<s) := (m r (by omega) c hc).2 hr
  cases v <;> fin_cases d <;>
    norm_num [available,neighbor,duoCode] at hr hc ae ⊢ <;>
    (try simp (disch := omega) only [Nat.sub_add_cancel])
  · have a := (vert (r-1) c (by omega) (by omega)).1
    have b := (vert (r-1) (c+1) (by omega) (by omega)).1
    simp (disch := omega) only [Nat.sub_add_cancel] at a b
    rw [a,b]
  · rw [(vert r c (by omega) (by omega)).2,(vert r (c+1) (by omega) (by omega)).2]
  · have a := (horiz r (c-1) (by omega) (by omega)).1
    have b := (horiz (r+1) (c-1) (by omega) (by omega)).1
    simp (disch := omega) only [Nat.sub_add_cancel] at a b
    rw [a,b]
  · rw [(horiz r c (by omega) (by omega)).2,(horiz (r+1) c (by omega) (by omega)).2]

private theorem updated {h w M A r c} {ds : List Duo} (old : Fits h w M A) (yes : M r c∈ds) :
    Fits h w M (A.setIfInBounds r ((A[r]?.getD #[]).setIfInBounds c ds)) := by
  intro x hx y hy
  by_cases R : r=x
  · subst x; by_cases H : r<A.size
    · unfold getPair; rw [Array.getElem?_setIfInBounds_self_of_lt H]; dsimp only [Option.getD_some]
      by_cases C : c=y
      · subst y; by_cases W : c<(A[r]?.getD #[]).size
        · rwa [Array.getElem?_setIfInBounds_self_of_lt W]
        · rw [Array.setIfInBounds,dif_neg W]; exact old _ hx _ hy
      · rw [Array.getElem?_setIfInBounds_ne C]; exact old _ hx _ hy
    · simpa only [Array.setIfInBounds,dif_neg H] using old _ hx _ hy
  · simpa only [getPair,Array.getElem?_setIfInBounds_ne R] using old x hx y hy

set_option maxHeartbeats 1200000 in
theorem pairSweep_sound {s M A} (e : Agree s M) (h : Kept s M A) (v : Bool) (fuel : Nat) :
    Kept s M (pairSweep s v fuel A) := by
  let H := s-v.toNat; let W := s-(!v).toNat
  let Z (r c : Nat) := (M r c,M (r+v.toNat) (c+(!v).toNat))
  have init : Fits H W Z (firstPair s v A) := by
    intro r hr c hc
    simp only [firstPair,getPair,mkSheet,Array.getElem?_ofFn,show r<s-v.toNat from hr,show c<s-(!v).toNat from hc,
      dite_true,Option.getD_some,bonds,List.mem_flatMap,List.mem_map,List.mem_filter,beq_iff_eq]
    refine ⟨_,h _ (by dsimp [H] at hr; omega) _ (by dsimp [W] at hc; omega),_,⟨h _ (by omega) _ (by omega),?_⟩,rfl⟩
    cases v <;> norm_num [H,W] at hr hc ⊢
    · exact ((e r hr c (by omega)).1 (by omega)).1
    · exact ((e r (by omega) c hc).2 (by omega)).1
  have step (G d r c) (hd : d<4) (hr : r<H) (hc : c<W) (old : Fits H W Z G) : Fits H W Z (pstep H W v d G r c) := by
    let x := if d<2 then r else H-1-r
    let y := if d<2 then c else W-1-c
    have X : x<H := by dsimp [x]; split <;> omega
    have Y : y<W := by dsimp [y]; split <;> omega
    let z := neighbor x y ((d+2)%4)
    change Fits H W Z (if available H W x y ((d+2)%4) then
      G.setIfInBounds x ((G[x]?.getD #[]).setIfInBounds y (narrow v d (getPair G z.1 z.2) (getPair G x y))) else G)
    by_cases adj : available H W x y ((d+2)%4)
    swap
    · simpa only [if_neg adj] using old
    rw [if_pos adj]
    have B : z.1<H ∧ z.2<W := by
      change available H W x y ((d+2)%4) at adj
      change (neighbor x y ((d+2)%4)).1<H ∧ (neighbor x y ((d+2)%4)).2<W
      generalize he : (d+2)%4=k at adj ⊢
      have hk : k<4 := he ▸ Nat.mod_lt _ (by decide)
      interval_cases k <;> simp [available,neighbor] at adj ⊢ <;> omega
    apply updated old; apply List.mem_filter.mpr
    refine ⟨old _ X _ Y,?_⟩
    simp only [Std.HashSet.contains_ofList,List.contains_iff_mem,List.mem_map]
    exact ⟨_,old _ B.1 _ B.2,lift_agree e v _ X _ Y ⟨d,hd⟩ adj⟩
  have keep (G) (old : Fits H W Z G) : Fits H W Z (tighten H W v fuel G) := by
    induction fuel generalizing G with
    | zero => exact old
    | succ t ih =>
      have nxt : Fits H W Z ((List.range 4).foldl (fun A d => ppass H W v d A) G) := by
        apply List.foldlRecOn (motive:=Fits H W Z) _ _ old; intro L live d hd
        unfold ppass; apply List.foldlRecOn (motive:=Fits H W Z) _ _ live; intro B ok r hr
        apply List.foldlRecOn (motive:=Fits H W Z) _ _ ok; intro K kept c hc
        exact step _ _ _ _ (List.mem_range.mp hd) (List.mem_range.mp hr) (List.mem_range.mp hc) kept
      unfold tighten; dsimp only; split <;> first | exact nxt | exact ih _ nxt
  have live := keep _ init
  intro r hr c hc; unfold pairSweep dropPair; rw [at_build hr hc]
  apply List.mem_filter.mpr; refine ⟨h r hr c hc, Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
  · apply Bool.or_eq_true_iff.mpr
    by_cases b : r+v.toNat<s ∧ c+(!v).toNat<s
    · right; simp only [Std.HashSet.contains_ofList,List.contains_iff_mem,List.mem_map]
      exact ⟨_,live r (by dsimp [H]; omega) c (by dsimp [W]; omega),rfl⟩
    · left; simp; omega
  · apply Bool.or_eq_true_iff.mpr
    by_cases b : v.toNat≤r ∧ (!v).toNat≤c
    · right; simp only [Std.HashSet.contains_ofList,List.contains_iff_mem,List.mem_map]
      exact ⟨_,live (r-v.toNat) (by dsimp [H]; omega) (c-(!v).toNat) (by dsimp [W]; omega),
        by simp only [Z,Nat.sub_add_cancel b.1,Nat.sub_add_cancel b.2]⟩
    · left; simp; omega
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
