import GridGraphs.NoPitch.TailRows.IncidenceChecks
import GridGraphs.NoPitch.TailRows.FacePatchFast

namespace GridGraphs.NoPitch.FiniteRows.Fast
open PitchCut Keys FaceRows LocalBoard19 GridGraphs.NoPitch.Dual TailRows TailRows.Incidence

/-- All mask-dependent words for the eight oriented views. The catalogue
has 100 legal masks and is shared by every actual patch position. -/
structure PatchWords where
  key : Vector Nat 8
  boundary : Vector (Vector Nat 8) 4
  cells : Vector (Vector (Vector Nat 8) 3) 3

def encode (a : Nine) : PatchWords := ⟨FacePatch.word a,
  Vector.ofFn fun d => Vector.ofFn fun g => word6 a g (dirView g d),
  Vector.ofFn fun u => Vector.ofFn fun t => Vector.ofFn fun g =>
    let q := (u,t); cellWord (small 3 g q) (a q) (patchBits a q g)⟩
def patterns := (FacePatch.masks.filter legal).map encode
private theorem exhaust : ∀ a : Nine, a∈FacePatch.masks := by native_decide

def sideKeys {k} (p : PatchPos k) := Vector.ofFn fun d => Vector.ofFn fun g => port 7 (patchFine p g) (dirView g d)
def cellKeys {k} (p : PatchPos k) := Vector.ofFn fun u => Vector.ofFn fun t => Vector.ofFn fun g => plug (patchFine p g) (small 3 g (u,t))

@[noinline] def applyWords (B : Book) (w : Nat → Terms) (origin : Vector Nat 8)
    (ports : Vector (Vector (Option Nat) 8) 4) (cells : Vector (Vector (Vector (Option Nat) 8) 3) 3) (m : PatchWords) :=
  let e := (List.finRange 4).flatMap fun d => viewSum fun g =>
    let ts := lookup B.P ports[d][g] m.boundary[d][g]
    if (dirView g d).val<2 then ts else negTerms ts
  let s := offsets.flatMap fun q => viewSum fun g => lookup B.S cells[q.1][q.2][g] m.cells[q.1][q.2][g]
  balanced (w (FacePatch.combine origin m.key) ++ negTerms (e++negTerms s))

@[noinline] def patchPass {k} (B : Book) (w : Nat → Terms) (p : PatchPos k) :=
  patterns.all (applyWords B w (FacePatch.origin p) (sideKeys p) (cellKeys p))

theorem patch_sound {k} (B w) (p : PatchPos k) (ok : patchPass B w p) : patchCheck w B p := by
  unfold patchCheck; simp only [decide_eq_true_eq]; intro a ha
  have mem : encode a∈patterns := List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨exhaust a,ha⟩,rfl⟩
  have z := List.all_eq_true.mp ok _ mem
  simpa only [applyWords,encode,Fin.getElem_fin,Vector.getElem_ofFn,sideKeys,cellKeys,FacePatch.combine_eq] using z

def incidenceCheck (D : Chart) (B : Book) (k : Nat) :=
  let w := contribution D (index D) (prices D B.sel)
  supported D B.sel && decide (∀ x : Site k, starCheck w B x) && decide (∀ p : PatchPos k, patchPass B w p)

theorem sound (D B k) (ok : incidenceCheck D B k) : Incidence.cert D B k := by
  simp only [incidenceCheck,Incidence.cert,Bool.and_eq_true,decide_eq_true_eq] at ok ⊢
  exact ⟨ok.1,fun p => patch_sound _ _ _ (ok.2 p)⟩
end GridGraphs.NoPitch.FiniteRows.Fast
