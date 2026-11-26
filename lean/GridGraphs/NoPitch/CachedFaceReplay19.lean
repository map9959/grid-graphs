import GridGraphs.NoPitch.FaceLineRows

namespace GridGraphs.NoPitch.CachedReplay
open PitchCut Keys Wired FaceRows GridGraphs.NoPitch.Dual

abbrev Pos := FacePos 6
abbrev Lookup := Nat → Terms
abbrev Stamps := Vector Terms 36

/-- Explicit call boundaries keep `decide` from moving the data supplied to
one level of the scan into the body of the next universal quantifier. -/
@[noinline] def positions (w : Lookup) (cost : Stamps) (vs : Vector Nat 8) :=
  decide (∀ p : Pos, balanced (w (keyAt p vs) ++ cost[(6*p.1.val+p.2.val)%36]))

@[noinline] def partitionsFor (w : Lookup) (cost : Stamps) (m : Mask) :=
  (catalog m).all fun z => positions w cost (faceViews m (partOf z))

def posOf (j : Fin 36) : Pos := (Fin.ofNat 6 (j.val/6),Fin.ofNat 6 j.val)

@[noinline] def scan (w : Lookup) (cost : Mask → Stamps) :=
  decide (∀ i : Fin 65536, let m := maskOf i
    fresh initial (rawEdges m) → partitionsFor w (cost m) m)

@[noinline] def patchScan (w : Lookup) :=
  scan w (fun m => Vector.ofFn fun j => children w (posOf j) m)

@[noinline] def lineScan (w : Lookup) :=
  scan w (fun m => Vector.ofFn fun j => FaceLines.neg (FaceLines.rotStamps m (posOf j)))

def patchOK (D : Chart) := patchScan (contribution D (index D) (signatures D))
def lineOK (D : Chart) := lineScan (contribution D (index D) (D.cols.map FaceLines.entries))

theorem scan_sound {w cost} (ok : scan w cost) (i : Fin 65536)
    (raw : fresh initial (rawEdges (maskOf i))) (z : Nat) (hz : z∈catalog (maskOf i)) (p : Pos) :
    balanced (w (keyAt p (faceViews (maskOf i) (partOf z))) ++
      (cost (maskOf i))[(6*p.1.val+p.2.val)%36]) := by
  have a := of_decide_eq_true ok i raw
  have b := List.all_eq_true.mp a z hz
  exact of_decide_eq_true b p

theorem patch_sound (D : Chart) (ok : patchOK D) : tileOK D := by
  unfold tileOK
  simp only [decide_eq_true_eq]
  intro i raw z hz p
  let w := contribution D (index D) (signatures D)
  exact scan_sound (w:=w) (cost:=fun m => Vector.ofFn fun j => children w (posOf j) m) ok i raw z hz p

theorem line_sound (D : Chart) (ok : lineOK D) : FaceLines.tileCheck D := by
  unfold FaceLines.tileCheck
  simp only [decide_eq_true_eq]
  intro i raw z hz p
  exact scan_sound (w:=contribution D (index D) (D.cols.map FaceLines.entries))
    (cost:=fun m => Vector.ofFn fun j => FaceLines.neg (FaceLines.rotStamps m (posOf j))) ok i raw z hz p

@[noinline] def steps (ch : Lookup) :=
  decide (∀ (r j : Fin 7), ∀ s∈LineKeys.states j.val, ∀ a : Letter, LineKeys.allowedStep j.val s a →
    let t := advance s a
    balanced (ch (LineKeys.key r j.val s t) ++ FaceLines.lineStamps (r,j) s t))

def stepOK (D : Chart) := steps (contribution D (index D) (D.cols.map FaceLines.entries))
theorem step_sound (D : Chart) (ok : stepOK D) : FaceLines.stepCheck D := ok

@[noinline] def unused (w : Lookup) :=
  decide (∀ p : PatchPos 6, missing p → ∀ a : Nine, w (patchCode p a)=[])
def unusedCached (D : Chart) := unused (contribution D (index D) (signatures D))
theorem unused_sound (D : Chart) (ok : unusedCached D) : unusedOK D := ok

end GridGraphs.NoPitch.CachedReplay
