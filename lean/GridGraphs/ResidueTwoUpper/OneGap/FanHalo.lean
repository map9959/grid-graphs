import GridGraphs.ResidueTwoUpper.OneGap.FanRootRepair
import GridGraphs.ResidueTwoUpper.OneGap.FanPortTile

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port.Halo
open FanSlab
abbrev Pattern := Nat × Nat × Nat × Nat
abbrev BoardNat := Array (Array (List Nat))
def tag (m d : Nat) := m+(d <<< 9)
def ms (z : Nat) := z%512
def dr (z : Nat) := z >>> 9
def key (incoming : Bool) (z d : Nat) := 2*ov d (ms z)+(if incoming then ((ms z).testBit 4 || (ms z).testBit ([5,7,3,1][d]!)) != (dr z==d) else dr z==d).toNat
def maskOf (p : Pattern) (y x : Nat) := if x<3 then (if y<3 then p.1 else p.2.1) else (if y<3 then p.2.2.1 else p.2.2.2)
def active (m d : Nat) := m.testBit 4 || m.testBit ([5,7,3,1][d]!)
def pinned (p : Pattern) (r c m : Nat) := (List.finRange 9).all fun k => let y := r+k.val/3; let x := c+k.val%3
  y<3 || x<3 || 9≤y || 9≤x || m.testBit k.val==(maskOf p (y-3) (x-3)).testBit (3*((y-3)%3)+(x-3)%3)
structure Atlas (p : Pattern) where
  data : Fin 10 → Fin 10 → Nat
  admit : ∀ r c, dr (data r c)<4 ∧ accepts (5+(r.val+1)%3) (5+(c.val+1)%3) (ms (data r c)) ∧ active (ms (data r c)) (dr (data r c)) ∧ pinned p r c (ms (data r c))
  right : ∀ r c t, c.val+1=t.val → key false (data r c) 0=key true (data r t) 2 ∧ key false (data r t) 2=key true (data r c) 0
  below : ∀ r s c, r.val+1=s.val → key false (data r c) 1=key true (data s c) 3 ∧ key false (data s c) 3=key true (data r c) 1

private def base (p : Pattern) : BoardNat := Array.ofFn fun r : Fin 10 => Array.ofFn fun c : Fin 10 =>
  (List.range 2048).filter fun z => accepts (5+(r.val+1)%3) (5+(c.val+1)%3) (ms z) && active (ms z) (dr z) && pinned p r c (ms z)
private def pos (r c : Fin 10) (G : BoardNat) := (G[r.val]!)[c.val]!
private def supported (d e z : Nat) (src : List Nat) := src.any fun t => key false t d==key true z e
private def sweep (G : BoardNat) := Array.ofFn fun r : Fin 10 => Array.ofFn fun c : Fin 10 => (pos r c G).filter fun z =>
  (r.val==0 || supported 1 3 z (pos (Fin.ofNat 10 (r.val-1)) c G)) && (r.val==9 || supported 3 1 z (pos (Fin.ofNat 10 (r.val+1)) c G)) &&
  (c.val==0 || supported 0 2 z (pos r (Fin.ofNat 10 (c.val-1)) G)) && (c.val==9 || supported 2 0 z (pos r (Fin.ofNat 10 (c.val+1)) G))
private def replay (p : Pattern) (k : Nat) := (sweep^[k]) (base p)
private theorem empty : ∀ p∈banned, (pos 5 5 (replay p 20)).isEmpty := by native_decide

theorem excludes (p : Pattern) (bad : p∈banned) (X : Atlas p) : False := by
  have live (k : Nat) : ∀ r c, X.data r c∈pos r c (replay p k) := by
    induction k with
    | zero => intro r c; obtain ⟨b,a,v,h⟩ := X.admit r c; have sz : X.data r c<2048 := by unfold dr at b; rw [Nat.shiftRight_eq_div_pow] at b; omega
              simp [pos,replay,base,r.isLt,c.isLt,sz,a,v,h]
    | succ k ih =>
      intro r c; simp only [replay,Function.iterate_succ_apply']
      unfold sweep pos; simp [r.isLt,c.isLt]; refine ⟨ih r c,⟨⟨?_,?_⟩,?_⟩,?_⟩
      · by_cases h : r.val=0; exact .inl (Fin.ext h)
        right; let s := Fin.ofNat 10 (r.val-1); have e : s.val+1=r.val := by dsimp [s,Fin.ofNat]; omega
        exact List.any_eq_true.mpr ⟨_,ih s c,beq_iff_eq.mpr (X.below _ _ _ e).1⟩
      · by_cases h : r.val=9; exact .inl h
        right; let s := Fin.ofNat 10 (r.val+1); have e : r.val+1=s.val := by dsimp [s,Fin.ofNat]; omega
        exact List.any_eq_true.mpr ⟨_,ih s c,beq_iff_eq.mpr (X.below _ _ _ e).2⟩
      · by_cases h : c.val=0; exact .inl (Fin.ext h)
        right; let t := Fin.ofNat 10 (c.val-1); have e : t.val+1=c.val := by dsimp [t,Fin.ofNat]; omega
        exact List.any_eq_true.mpr ⟨_,ih r t,beq_iff_eq.mpr (X.right _ _ _ e).1⟩
      · by_cases h : c.val=9; exact .inl h
        right; let t := Fin.ofNat 10 (c.val+1); have e : c.val+1=t.val := by dsimp [t,Fin.ofNat]; omega
        exact List.any_eq_true.mpr ⟨_,ih r t,beq_iff_eq.mpr (X.right _ _ _ e).2⟩
  simpa [List.isEmpty_iff.mp (empty p bad)] using live 20 5 5
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port.Halo
