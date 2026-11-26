import GridGraphs.NoPitch.FiniteRows.Normalization
import GridGraphs.NoPitch.TailRows.FacePatchFast
namespace GridGraphs.NoPitch.FiniteRows.Fast
open PitchCut Keys FaceRows LocalBoard19 GridGraphs.NoPitch.Dual TailRows
private theorem cover : ∀ a : Nine, a∈FacePatch.masks := by native_decide

@[noinline] def blankWords (w : Nat → Terms) (x : Vector Nat 8) (ts : Terms) :=
  FacePatch.words.all fun m => balanced (w (FacePatch.combine x m) ++ negTerms ts)

@[noinline] def normSites (k : Nat) (w : Nat → Terms) :=
  decide (∀ x : Site k, starNormAt w x (w (emptyStar x))) &&
  decide (∀ p : PatchPos k, blankWords w (FacePatch.origin p) (w (emptyPatch p)))

def normalizationCheck (D : Chart) (k stop : Nat) :=
  let w := contribution D (index D) (prices D (norms stop))
  supported D (norms stop) && normSites k w && normalTotals D k stop w

theorem norm_sound (D k stop) (ok : normalizationCheck D k stop) : normCheck D k stop := by
  simp only [normalizationCheck,normCheck,normalSites,normSites,Bool.and_eq_true,decide_eq_true_eq] at ok ⊢
  refine ⟨⟨ok.1.1,ok.1.2.1,?_⟩,ok.2⟩
  intro p; unfold patchNormAt; simp only [decide_eq_true_eq]; intro a ha
  have mem : FacePatch.word a∈FacePatch.words := List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨cover a,ha⟩,rfl⟩
  simpa only [FacePatch.combine_eq] using List.all_eq_true.mp (ok.1.2.2 p) _ mem
end GridGraphs.NoPitch.FiniteRows.Fast
