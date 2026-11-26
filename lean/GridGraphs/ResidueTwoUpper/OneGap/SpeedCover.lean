import GridGraphs.Geometry.SynchronousFront

/-! Arithmetic schedule from the odd-fan handoff to a checked-size south
cap. This theorem is about reachability by the published window sizes;
it does not assume or assert that any particular physical window is empty.
For the finite range a batched greedy schedule suffices, with one explicit
exception `(207,205)`; hence no table of 67,467 schedules is stored. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Speed

structure Move where
  s : Nat
  d : Nat
  width : Nat
  height : Nat
  rooted : Bool
deriving DecidableEq

def long : Move := ⟨27,13,14,34,false⟩
def medium : Move := ⟨20,10,11,27,false⟩
def short : Move := ⟨13,7,8,20,false⟩
def tiny : Move := ⟨6,4,5,13,false⟩
def root : Move := ⟨4,3,10,10,true⟩
def moves := [long,medium,short,tiny,root]
abbrev State := Nat × Nat  -- rows remaining, first established suffix column
def start (k q : Nat) : State :=
  let y := (q-15)/6
  (k-(y+6), q-3*y+3)
def cap (k : Nat) (p : State) : Prop :=
  14≤p.1 ∧ p.1≤43 ∧ p.2+(3*p.1)/4+3≤k
instance (k p) : Decidable (cap k p) := by unfold cap; infer_instance
def x (m : Move) (q f : Nat) := if m.rooted then max f (q+1) else f
def fits (k q : Nat) (m : Move) (p : State) : Prop :=
  x m q p.2 + m.width + 7 ≤ k ∧
  (m.rooted=false → x m q p.2 + m.width ≤ q+1) ∧ m.height+7≤p.1
instance (k q m p) : Decidable (fits k q m p) := by unfold fits; infer_instance
def next (m : Move) (q : Nat) (p : State) : State := (p.1-m.s,x m q p.2+m.d)

inductive Reaches (k q : Nat) : State → Prop
  | capEnd (p) : cap k p → Reaches k q p
  | via (p m) : m∈moves → fits k q m p → Reaches k q (next m q p) → Reaches k q p

private def run (_k q : Nat) (m : Move) (a : Nat) (p : State) : State :=
  if a=0 then p else (p.1-a*m.s,x m q p.2+a*m.d)

private theorem repeatMove {k q m a p} (hm : m∈moves)
    (nonzero : 0<a → x m q p.2+(a-1)*m.d+m.width+7 ≤ k ∧
      (m.rooted=false → x m q p.2+(a-1)*m.d+m.width ≤ q+1) ∧
      (a-1)*m.s+m.height+7 ≤ p.1) (finish : Reaches k q (run k q m a p)) : Reaches k q p := by
  induction a generalizing p with
  | zero => simpa [run] using finish
  | succ a ih =>
    obtain ⟨room,end',h⟩ := nonzero (by omega)
    simp only [Nat.add_one_sub_one] at room end' h
    refine .via p m hm ⟨by omega,fun e => by have := end' e; omega,by omega⟩ ?_
    have xeq : x m q (next m q p).2=x m q p.2+m.d := by
      unfold next x; split <;> simp_all <;> omega
    have sh : (next m q p).1=p.1-m.s := rfl
    apply ih (p:=next m q p)
    · intro pos
      have d := Nat.succ_mul (a-1) m.d
      have s := Nat.succ_mul (a-1) m.s
      rw [show (a-1).succ=a by omega] at d s
      rw [xeq,sh]
      exact ⟨by omega,fun e => by have := end' e; omega,by omega⟩
    · cases a with
      | zero => simpa [run,next] using finish
      | succ a =>
        simpa only [run,Nat.succ_ne_zero,if_false,xeq,sh,Nat.succ_mul,Nat.sub_sub,
          Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using finish

private def batch (k q : Nat) (m : Move) (p : State) : Nat :=
  let lim := if m.rooted then k else min (k-8) q
  let maxX := min (k-8) lim
  let f := x m q p.2
  if f+m.width>maxX+1 ∨ p.1 < max 44 (m.height+7) then 0 else
    min ((maxX+1-(f+m.width))/m.d+1) ((p.1-max 44 (m.height+7))/m.s+1)

private def schedule (k q : Nat) (p : State) : List (Move × Nat) → Bool
  | [] => decide (cap k p)
  | (m,a)::rest =>
    decide (cap k p) || (decide (m∈moves) &&
      (a==0 || decide (x m q p.2+(a-1)*m.d+m.width+7 ≤ k ∧
        (m.rooted=false → x m q p.2+(a-1)*m.d+m.width ≤ q+1) ∧
        (a-1)*m.s+m.height+7≤p.1)) && schedule k q (run k q m a p) rest)

private theorem sound {k q p steps} (h : schedule k q p steps) : Reaches k q p := by
  induction steps generalizing p with
  | nil => exact .capEnd p (of_decide_eq_true h)
  | cons item rest ih =>
    obtain ⟨m,a⟩ := item
    simp only [schedule,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
    rcases h with cap|⟨⟨hm,b⟩,tail⟩
    · exact .capEnd p cap
    · exact repeatMove hm (fun pos => b.resolve_left (by omega)) (ih tail)

private def greedy (k q : Nat) (p : State) : List Move → List (Move × Nat)
  | [] => []
  | m::rest => let a := batch k q m p; (m,a)::greedy k q (run k q m a p) rest
private def bounded (t i : Nat) :=
  let k := 207+14*t
  let q := 57+2*i
  decide (k≥2000 ∨ k<q+2) || schedule k q (start k q)
    (if k=207 ∧ q=205 then [(short,1),(long,5)] else greedy k q (start k q) moves)
private theorem boundedCheck : ∀ t : Fin 129, ∀ i : Fin 971, bounded t i := by native_decide

theorem finite_cover {k q : Nat} (hk : k=207+14*((k-207)/14)) (upper : k<2000)
    (lo : 57≤q) (hi : q+2≤k) (odd : q%2=1) : Reaches k q (start k q) := by
  let t : Fin 129 := ⟨(k-207)/14,by omega⟩
  let i : Fin 971 := ⟨(q-57)/2,by omega⟩
  have h := boundedCheck t i
  unfold bounded at h
  dsimp only [t,i] at h
  rw [← hk,show 57+2*((q-57)/2)=q by omega] at h
  simp only [show ¬(k≥2000 ∨ k<q+2) by omega,decide_false,Bool.false_or] at h
  exact sound h

def widthRoom (k : Nat) (m : Move) (p : State) : Prop :=
  p.2+3*((m.height-2)/4)+(m.height-2)%4+8≤k
instance (k m p) : Decidable (widthRoom k m p) := by unfold widthRoom; infer_instance

/-- A schedule with enough physical room to prove every read straight. -/
inductive RoomyWith (ms : List Move) (k q : Nat) : State → Prop
  | capEnd (p) : cap k p → RoomyWith ms k q p
  | via (p m) : m∈ms → fits k q m p → widthRoom k m p →
      RoomyWith ms k q (next m q p) → RoomyWith ms k q p

abbrev Roomy := RoomyWith moves
def extended : Move := ⟨48,22,23,55,false⟩
abbrev ExtendedRoute := RoomyWith (extended :: moves)

theorem Roomy.extend {k q p} (route : Roomy k q p) : ExtendedRoute k q p := by
  induction route with
  | capEnd p cap => exact .capEnd p cap
  | via p m mem fit wide _ ih => exact .via p m (List.mem_cons_of_mem _ mem) fit wide ih

theorem Roomy.reaches {k q p} (route : Roomy k q p) : Reaches k q p := by
  induction route with
  | capEnd p h => exact .capEnd p h
  | via p m mem fit _ _ ih => exact .via p m mem fit ih

/-- Use the long dangling move while it fits before the first root;
on switching, the remaining rooted slope already fits the cap. -/
theorem roomy_uniform {k q : Nat} (hk : 235≤k) (lo : 57≤q) (hi : q+2≤k)
    (odd : q%2=1) : Roomy k q (start k q) := by
  let y := (q-15)/6
  have span : 6*y+15≤q ∧ q≤6*y+19 := by dsimp [y]; omega
  let f (m : Nat) := q-3*y+3+13*m
  let h (m : Nat) := k-(y+6+27*m)
  have room (m : Nat) (hh : 14≤h m) :
      (h m≤40 → cap k (h m,f m)) ∧ (41≤h m → f m+33≤k) ∧
      (f m+14>q+1 → 41≤h m → q+1+3*(h m)/4+3≤k) := by
    dsimp [f,h,cap] at *; refine ⟨?_,?_,?_⟩ <;> omega
  have go (m : Nat) (hh : 14≤h m) (front : f m≤q+1) : Roomy k q (h m,f m) := by
    generalize eh : h m=H at hh ⊢
    induction H using Nat.strong_induction_on generalizing m with
    | h H ih =>
      subst H
      by_cases stop : h m≤40
      · exact .capEnd _ ((room _ hh).1 stop)
      by_cases dangling : f m+14≤q+1
      · have space := (room _ hh).2.1 (by omega)
        apply RoomyWith.via _ long (by decide)
        · simpa [fits,x,long] using (show f m+14+7≤k ∧ f m+14≤q+1 ∧ 34+7≤h m by omega)
        · change f m+24+8≤k; omega
        · have j : h (m+1)=h m-27 := by dsimp [h]; omega
          have g : f (m+1)=f m+13 := by dsimp [f]; omega
          have ne := ih (h (m+1)) (by omega) (m+1) (by omega) rfl (by omega)
          simpa [next,x,long,j,g] using ne
      · have all := (room _ hh).2.2 (by omega) (by omega)
        let L := (h m-16)/4
        have fin : 16≤h m-4*L ∧ h m-4*L≤19 := by dsimp [L]; omega
        have pos : 0<L := by dsimp [L]; omega
        have tail (n : Nat) (lim : n ≤ L) : Roomy k q (h m-4*(L-n),q+1+3*(L-n)) := by
          induction n with
          | zero =>
            apply RoomyWith.capEnd; dsimp [cap]; omega
          | succ n ih =>
            apply RoomyWith.via _ root (by decide)
            · simp [fits,x,root]; omega
            · change q+1+3*(L-(n+1))+6+8≤k; omega
            · simpa only [next,x,root,ite_true,max_eq_left (show q+1≤q+1+3*(L-(n+1)) by omega),
                show h m-4*(L-(n+1))-4=h m-4*(L-n) by omega,
                show q+1+3*(L-(n+1))+3=q+1+3*(L-n) by omega] using ih (by omega)
        apply RoomyWith.via _ root (by decide)
        · simp [fits,x,root,max_eq_right front]; omega
        · change f m+6+8≤k; omega
        · simpa only [next,x,root,ite_true,max_eq_right front,show L-(L-1)=1 by omega,
            Nat.mul_one] using tail (L-1) (by omega)
  exact go 0 (by dsimp [h,y]; omega) (by dsimp [f,y]; omega)

theorem large_cover {k q : Nat} (hk : 2000≤k) (lo : 57≤q) (hi : q+2≤k)
    (odd : q%2=1) : Reaches k q (start k q) :=
  (roomy_uniform (by omega) lo hi odd).reaches

theorem cover (u q : Nat) (lo : 57≤q) (hi : q+2≤207+14*u) (odd : q%2=1) :
    Reaches (207+14*u) q (start (207+14*u) q) := by
  by_cases h : 207+14*u<2000
  · exact finite_cover (by omega) h lo hi odd
  · exact large_cover (by omega) lo hi odd

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Speed
