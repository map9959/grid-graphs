import GridGraphs.ResidueTwoUpper.OneGap.FanCollision
import GridGraphs.ResidueTwoUpper.OneGap.EastBoundaryKernel

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
open L7 FanSlab FanSweep

/-- Eastern end of a fan row in physical mask order. `b` is the
first plain tile, and `c` is in the same aligned tile coordinates. -/
def edge (b c : Nat) := if c+3<b then 146 else if c+3=b then 18 else
  if c+2=b then 66 else if c+1=b then 72 else 73

def box (L R : Nat) : Box := ⟨15,3*(L+R),[]⟩
def pins (seed : Bool) (L j b r c m : Nat) : Bool :=
  if c%3 != 0 then true else
  if r=3*j ∧ L<b ∧ L<c/3 then m==edge b (c/3) else
  if seed then
    let q := b+3*j-2
    r != 0 || (if c/3<q then lane m 4==1 else m==(if c/3=q then 64 else 72))
  else r>3 || r%3 != 0 || m==edge (b+6-r) (c/3)
def priceTable := Array.ofFn fun a : Fin 8 => Array.ofFn fun e : Fin 3 =>
  (List.range 512).filter fun m => accepts a.val (5+e.val) m
def chart (seed : Bool) (L R j b : Nat) := build (box L R) fun r c =>
  let a := if seed then rowTag r else 5+(r+1)%3
  (if seed && r==0 && c==3*(b+3*j-2) then List.range 512 else (priceTable[a]!)[(c+1)%3]!).filter
    (pins seed L j b r c)
theorem chart_mem {seed L R j b r c m} (rh : r<16) (ch : c≤3*(L+R)) (bd : m<512)
    (reg : ((seed && r==0 && c==3*(b+3*j-2)) ||
      accepts (if seed then rowTag r else 5+(r+1)%3) (5+(c+1)%3) m)=true)
    (pin : pins seed L j b r c m) : m∈cell (chart seed L R j b) r c := by
  simp [cell,chart,build,box,show c<3*(L+R)+1 by omega,rh,pin]
  split
  · exact List.mem_range.mpr bd
  · rename_i neg
    have good := (Bool.or_eq_true_iff.mp reg).resolve_left (by simpa using neg)
    have tag : (if seed then rowTag r else 5+(r+1)%3)<8 := by unfold rowTag; split_ifs <;> omega
    simp [priceTable,tag,show (c+1)%3<3 by omega,bd,good]
def goal (L j b : Nat) (G : Grid) := (cell G (3*j) (3*L)).all fun m => m==edge b L
def trial (seed : Bool) (L R j b : Nat) :=
  goal L j b (Kernel.prune 16 (3*(L+R)+1) (if seed && j==3 then 100 else 36) (chart seed L R j b))

private theorem key_mem {d x xs} (hit : x∈xs) :
    (Kernel.keys d xs).contains (Kernel.key d x)=true := by
  rw [Kernel.keys,Std.HashSet.contains_ofList,List.contains_iff_mem]
  exact List.mem_map_of_mem (f:=Kernel.key d) hit

theorem flat_sound {h w} (M : Nat → Nat → Nat)
    (ns : ∀ r c, r+1<h → c<w → ov 1 (M r c)=ov 3 (M (r+1) c))
    (ew : ∀ r c, r<h → c+1<w → ov 0 (M r c)=ov 2 (M r (c+1)))
    (n : Nat) (G : Grid) (keep : ∀ r<h, ∀ c<w, M r c∈Kernel.get G r c) :
    ∀ r<h, ∀ c<w, M r c∈Kernel.get (Kernel.prune h w n G) r c := by
  induction n generalizing G with
  | zero => exact keep
  | succ n ih =>
    apply ih
    intro r hr c hc
    simp [Kernel.pass,Kernel.get,hr,hc]
    refine ⟨keep r hr c hc,⟨⟨⟨?_,?_⟩,?_⟩,?_⟩⟩
    · by_cases z : r=0
      · exact .inl z
      · right; have e := ns (r-1) c (by omega) hc
        rw [show r-1+1=r by omega] at e
        change Kernel.key 1 _=Kernel.key 3 _ at e
        rw [←e]; exact key_mem (keep _ (by omega) _ hc)
    · by_cases z : r+1=h
      · exact .inl z
      · right; have e := ns r c (by omega) hc
        change Kernel.key 1 _=Kernel.key 3 _ at e
        rw [e,min_eq_right (by omega : r+1≤h-1)]; exact key_mem (keep _ (by omega) _ hc)
    · by_cases z : c=0
      · exact .inl z
      · right; have e := ew r (c-1) hr (by omega)
        rw [show c-1+1=c by omega] at e
        change Kernel.key 0 _=Kernel.key 2 _ at e
        rw [←e]; exact key_mem (keep _ hr _ (by omega))
    · by_cases z : c+1=w
      · exact .inl z
      · right; have e := ew r c hr (by omega)
        change Kernel.key 0 _=Kernel.key 2 _ at e
        rw [e,min_eq_right (by omega : c+1≤w-1)]; exact key_mem (keep _ hr _ (by omega))

private def checks (seed : Bool) (L j : Nat) (nonplain : Bool) :=
  (List.range 13).all fun t => (nonplain && t==0) || trial seed L 7 j (L+t)
private theorem certified :
    checks true 8 2 false && checks true 11 3 false &&
    checks false 4 2 false && checks false 3 2 true := by native_decide

inductive Mode : Bool → Nat → Nat → Prop
  | seedTwo : Mode true 8 2
  | seedThree : Mode true 11 3
  | boundary : Mode false 4 2
  | interior : Mode false 3 2

theorem replay {seed L j b} (mode : Mode seed L j) (lo : L≤b) (hi : b≤L+12)
    (strict : L=3 → L<b) : trial seed L 7 j b := by
  have tab := certified
  simp only [Bool.and_eq_true] at tab
  have use {s l y n} (ck : checks s l y n) (low : l≤b) (high : b≤l+12)
      (nz : n=true → l<b) : trial s l 7 y b := by
    have z := List.all_eq_true.mp ck (b-l) (List.mem_range.mpr (by omega))
    rw [show l+(b-l)=b by omega] at z
    rcases Bool.or_eq_true_iff.mp z with p|p
    · obtain ⟨a,c⟩ := Bool.and_eq_true_iff.mp p; have := beq_iff_eq.mp c; have := nz a; omega
    · exact p
  cases mode
  · exact use tab.1.1.1 lo hi (fun h => Bool.noConfusion h)
  · exact use tab.1.1.2 lo hi (fun h => Bool.noConfusion h)
  · exact use tab.1.2 lo hi (fun h => Bool.noConfusion h)
  · exact use tab.2 lo hi (fun _ => strict rfl)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.EastBoundary
