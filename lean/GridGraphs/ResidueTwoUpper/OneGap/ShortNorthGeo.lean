import GridGraphs.ResidueTwoUpper.OneGap.ShortKernelProof

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
open L7 ResidueZero Stencil

def baseWest (k v : Nat) := 9-min 3 (k-v-16)
def coordAt (k v : Nat) (far : Bool) (i : Nat) :=
  (if far then 3*k-48-3*v else 3*v)+i
def loc (k v : Nat) (w : View) (r c : Nat) :=
  (coordAt k (if w.swap then v else 0) w.rowFar r,
   coordAt k (if w.swap then 0 else v) w.colFar c)

theorem loc_bounds {k v r c} (room : v+16≤k) (w : View) (hr : r<48) (hc : c<48) :
    let a := loc k v w r c
    a.1<3*k ∧ a.2<3*k := by
  cases w with | mk a b t => cases a <;> cases b <;> cases t <;> simp [loc,coordAt] <;> omega

theorem normalized {k v r c} (room : v+16≤k) (w : View) (hr : r<48) (hc : c<48) :
    let a := loc k v w r c
    let b := unview w 48 r c
    unview w (3*k) a.1 a.2=(b.1,3*v+b.2) := by
  cases w with | mk a b t => cases a <;> cases b <;> cases t <;> simp [unview,loc,coordAt] <;> omega

/-- A window has its true eastern fringe if it comes within three tiles
of it. Otherwise no origin (or its center star) has an eastern tag. -/
theorem tags (u v : Nat) (west : 3≤v) (room : v+16≤11+14*u) (w : View) (r c : Nat) (hr : r<48) (hc : c<48) :
    let a := loc (11+14*u) v w r c
    let b := loc 25 (baseWest (11+14*u) v) w r c
    (tag u a.1,tag u a.2)=(tag 1 b.1,tag 1 b.2) := by
  have ax (j) (hj : j<48) (v' : Nat) (V : v'=0 ∨ v'=v) (far : Bool) :
      tag u (coordAt (11+14*u) v' far j)=
        tag 1 (coordAt 25 (if v'=0 then 0 else baseWest (11+14*u) v) far j) := by
    rcases V with rfl|rfl
    · cases far <;> dsimp [coordAt,tag] <;> split_ifs <;> omega
    · cases far <;> dsimp [coordAt,tag,baseWest] <;> split_ifs <;> omega
  cases w with | mk a b t =>
    cases t <;> apply Prod.ext <;> simp only [loc,Bool.false_eq_true,if_false,if_true] <;> first
      | exact ax r hr 0 (.inl rfl) a
      | exact ax c hc 0 (.inl rfl) b
      | simpa only [if_neg (by omega : v≠0)] using ax r hr v (.inr rfl) a
      | simpa only [if_neg (by omega : v≠0)] using ax c hc v (.inr rfl) b

theorem moveAgree {s M} (h : Agree s M) (a b : Nat) (room : a+48 ≤ s ∧ b+48 ≤ s) :
    Agree 48 (fun r c => M (a+r) (b+c)) := by
  intro r hr c hc; exact ⟨fun _ => (h (a+r) (by omega) (b+c) (by omega)).1 (by omega),
    fun _ => (h (a+r) (by omega) (b+c) (by omega)).2 (by omega)⟩
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short.North
