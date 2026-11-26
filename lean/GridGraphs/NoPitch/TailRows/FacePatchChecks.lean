import GridGraphs.NoPitch.TailRows.FacePatchGeometry

namespace GridGraphs.NoPitch.TailRows.FacePatch
open PitchCut Keys Wired FaceRows Budget LocalBoard19 GridGraphs.NoPitch.Dual

abbrev Lookup := Nat → Terms

def proxy (b : Nat) (t : FacePos 3) (r c : Nat) : PatchPos (max 3 b) :=
  haveI : NeZero (N (max 3 b)-2) := ⟨by unfold N; omega⟩
  (Fin.ofNat _ (patchAx b t.1 r), Fin.ofNat _ (patchAx b t.2 c))

def stamp (w : Lookup) (b : Nat) (t : FacePos 3) (r c : Nat) (a : Nine) : Terms :=
  if r=2 ∨ c=2 then [] else w (patchCode (proxy b t r c) a)

def kids (w : Lookup) (b : Nat) (t : FacePos 3) (m : Mask) :=
  corners.flatMap fun d => stamp w b t d.1 d.2 (slice m d)

def tagged (tags : Array Nat) (i : Nat) := tags[i]! == 6
def selector (D : Chart) := tagged (supportMasks D)

def support (D : Chart) (s : Nat → Bool) := D.cols.all fun c =>
  c.key%8==2 || c.key%8==4 || c.terms.all (fun t => !s t.1)

@[noinline] def patchScan (w : Lookup) (found : Nat → Bool) (b : Nat) :=
  decide (∀ p : PatchPos b, ∀ a : Nine, legal a →
    let key := patchCode p a
    found key && balanced (w key ++ negTerms (stamp w b (patchBand p) (p.1.val%3) (p.2.val%3) a)))

@[noinline] def posScan (w : Lookup) (found : Nat → Bool) (cost : FacePos 3 → Terms) (vs : Vector Nat 8) :=
  decide (∀ t : FacePos 3, let key := keyAt t vs; found key && balanced (w key ++ cost t))

@[noinline] def partScan (w : Lookup) (found : Nat → Bool) (b : Nat) (m : Mask) :=
  let cs := Vector.ofFn (n:=9) fun i => kids w b (Fin.ofNat 3 (i.val/3),Fin.ofNat 3 i.val) m
  (catalog m).all fun z => posScan w found (fun t => cs[(3*t.1.val+t.2.val)%9]) (faceViews m (partOf z))

@[noinline] def faceScan (w : Lookup) (found : Nat → Bool) (b : Nat) :=
  decide (∀ i : Fin 65536, let m := maskOf i; fresh initial (rawEdges m) → partScan w found b m)

@[noinline] def checkTags (D : Chart) (b : Nat) (tags : Array Nat) :=
  let s := tagged tags; let m := index D; let w := contribution D m (prices D s)
  let found := fun key => (locate D m key).isSome
  support D s && patchScan w found b && faceScan w found b

def cert (D : Chart) (b : Nat) := checkTags D b (supportMasks D)

end GridGraphs.NoPitch.TailRows.FacePatch
