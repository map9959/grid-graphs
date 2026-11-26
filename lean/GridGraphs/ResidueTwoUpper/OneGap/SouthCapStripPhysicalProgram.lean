import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripGridSchedule

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 Camera FanSeed SimpleGraph
namespace GridScan

def scanPoint (B : SiteBox) (axis : Axis) (j i : Nat) : Pos :=
  match axis with
  | .horizontal => (B.north+i,B.west+j)
  | .vertical => (B.north+j,B.west+i)

instance {h : Nat} (s : Window h (width h)) (j i : Int) : Decidable (EngineRimContact s j i) := by
  unfold EngineRimContact AcrossClosed
  infer_instance

instance {h : Nat} (s : Window h (width h)) (j i : Int) : Decidable (EngineOpenSite s j i) := by
  unfold EngineOpenSite AcrossClosed
  infer_instance

/-- Program for a physical crop. Open flags and teeth are set at
individual physical sites, not at entire tiles. The optional north
wire is selected by the strip placement, never by the mark bits. -/
def physicalProgram {u h : Nat} (s : Window h (width h)) (F : Finset (Site u))
    (v : View) (north : Bool) : Row.Program (3*s.depth) where
  mark j i := bitAt F v (scanPoint (prefixBox s (11+14*u) (3*s.length)) s.axis j i)
  tooth j i :=
    decide (EngineRimContact s j i) ||
      (north && decide (scanPoint (prefixBox s (11+14*u) (3*s.length)) s.axis j i =
        ((firstRow (11+14*u) h : Int)+1,((1+3*(11+14*u-1):Nat):Int))))
  exits j i := decide (EngineOpenSite s j i)

/-- The row reached by the coordinate chart uses exactly the engine
indices. Width and length here count physical sites, not tiles. -/
theorem scanPoint_offsets {h : Nat} (s : Window h (width h)) (k used j i : Nat) :
    let B := prefixBox s k used
    alongOffset s.axis B (scanPoint B s.axis j i)=(j:Int) ∧
      acrossOffset s.axis B (scanPoint B s.axis j i)=(i:Int) := by
  cases a : s.axis <;> simp [prefixBox,scanPoint,alongOffset,acrossOffset,a]

theorem scanPoint_contains {h : Nat} (s : Window h (width h)) (k used j i : Nat) :
    (prefixBox s k used).Contains (scanPoint (prefixBox s k used) s.axis j i) ↔
      j<used ∧ i<3*s.depth := by
  cases a : s.axis <;>
    simp [prefixBox,scanPoint,SiteBox.Contains,a] <;> omega

theorem scanPoint_prefix {h : Nat} (s : Window h (width h)) (k a b j i : Nat) :
    scanPoint (prefixBox s k a) s.axis j i=scanPoint (prefixBox s k b) s.axis j i := by
  cases ax : s.axis <;> simp [prefixBox,scanPoint,ax]

theorem scanPoint_board {u h : Nat} (s : Window h (width h)) (hk : 59≤11+14*u)
    (lo : 14≤h) (hi : h≤43) {used j i : Nat}
    (size : used≤3*s.length) (jl : j<used) (il : i<3*s.depth) :
    Camera.In (35+42*u) (scanPoint (prefixBox s (11+14*u) used) s.axis j i) := by
  have q := (scanPoint_contains s (11+14*u) used j i).mpr ⟨jl,il⟩
  have b := prefix_bounds s hk lo hi size
  dsimp only at b
  unfold SiteBox.Contains at q
  unfold Camera.In
  omega

theorem physical_program_mark {u h : Nat} (s : Window h (width h)) (F : Finset (Site u))
    (v : View) (north : Bool) (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (j : Nat) (i : Fin (3*s.depth)) (jl : j<3*s.length) :
    (physicalProgram s F v north).mark j i=true ↔
    point u v (scanPoint (prefixBox s (11+14*u) (3*s.length)) s.axis j i)∈F := by
  have on := scanPoint_board s hk lo hi le_rfl jl i.isLt
  simp only [physicalProgram,bitAt,←coord_point (w:=v) on,marked_at,decide_eq_true_eq]

def Mark {n : Nat} (p : Row.Program n) : Vertex n → Prop
  | none | some (0,_) => False
  | some (j+1,i) => p.mark j i=true

def Open {n : Nat} (p : Row.Program n) : Vertex n → Prop
  | none => True
  | some (0,_) => False
  | some (j+1,i) => p.exits j i=true

/-- The grid schedule supplies the same graph for every step of the
packed machine. Only component closure and global acyclicity remain
external to this interpretation. -/
def realization {n : Nat} (p : Row.Program n) (length : Nat)
    (close : ∀ j<length, RowClosure (graph p (j+1)) (slots n j) (Mark p) (Open p) (Row.drop n) Row.keep) :
    Row.Realization p length (graph p length) (Mark p) (Open p) where
  graph := graph p
  frontier := frontier n
  slots := slots n
  injective j _ := slots_injective n j
  reuses j _ := slots_reuses n j
  retains j _ := slots_retains n j
  newIsolated j _ i := by rw [slots_new]; exact graph_new_isolated p j i
  marks j _ i := by rw [slots_new]; rfl
  opens j _ i := by rw [slots_new]; rfl
  subgraph j hj := graph_mono p (le_of_lt hj)
  schedule _ hj := graph_schedule p hj
  advances j _ := graph_advance p j
  closure := close

theorem frontier_injective (n j : Nat) : Function.Injective (frontier n j) := by
  intro i k h
  apply Fin.ext
  have eq := slots_injective n j (show slots n j (Row.oldSlot i)=slots n j (Row.oldSlot k) by
    simpa only [slots_old] using h)
  exact congrArg (Fin.val : Fin (n+1+n) → Nat) eq

theorem grid_base_reflects {n : Nat} (p : Row.Program n) (size : n+1≤16) :
    (Partition.unpack (n+1) (Row.basePartition n).pack).Reflects (graph p 0)
      (frontier n 0) (Mark p) (Open p) := by
  rw [graph_zero]
  apply Row.base_reflects size (frontier_injective n 0)
  · intro i
    refine Fin.lastCases ?_ (fun x => ?_) i <;> simp [Mark,site]
  · intro i
    refine Fin.lastCases ?_ (fun x => ?_) i <;> simp [Open,site,Fin.ext_iff]
    have h := x.isLt
    omega

/-- An accepted run for the exact generated lattice graph, with no
external hypotheses about initialization or the row edge schedule. -/
theorem run_grid_accepts {n length : Nat} (p : Row.Program n) (size : n+1≤16)
    (acy : (graph p length).IsAcyclic)
    (close : ∀ j<length, RowClosure (graph p (j+1)) (slots n j) (Mark p) (Open p) (Row.drop n) Row.keep)
    (final : ∀ i, ComponentFlag (graph p length) (Mark p) (frontier n length i) →
      ComponentFlag (graph p length) (Open p) (frontier n length i)) :
    ∃ t, p.run (Row.basePartition n).pack length=some t ∧ Row.Program.accepts n t=true :=
  Row.packed_run_accepts (realization p length close) acy size (grid_base_reflects p size) final

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
