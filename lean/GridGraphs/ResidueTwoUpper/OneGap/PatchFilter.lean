import GridGraphs.ResidueTwoUpper.OneGap.DefectSites

/-! Radius-two overlap consistency of admissible patches around the unique
charged patch. Each domain also tests the zero-price star at its center. -/
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.PatchFilter
open ResidueZero Stencil

def table : Array Nat := #[
  0x5000000000000000f000000000000030000001313000003cc000000000000005500000000000500df00001311000033cc01011313010533cc,
  0x5000000000000000b000000000000000000000111000023cc0000000000000051000000000005009300000131000003cc01010111010503cc,
  0x5000000000000000f000000110000000000001333000003cc000000000000005500000000000500df00001311000013cc01011333010513cc,
  0x100000000000000050000000000000308000012130000030c00000000000000310000000000050055000012110000330001010013010533cc,
  0x17000000000000001f000000110000030000001333000003ce000000000000005700000000000500df00001311000033dc01011333010533cc,
  0x10000000000000023000000110000004000001233000003000000000000000005000000000005000f000012110000134401010033010513cc,
  0x17000000000000001f0000000000000300000013130000030c000000000000005700000000000500df000013110000334401011313010533cc,
  0x17000000000000001b0000000200001000000000130000000c00000000000000530000000000050093000000000000134401011313010513cc,
  0x17000000000000001f0000001100000000000013330000030c000000000000005700000000000500df000013110000134401011333010513cc,
  0x104c00000000000030000000000000000000000000000000002000000002000000000000000000000000,
  0x20000000000000000000000000000000000000000000000000000020000000002000002000,
  0x20000004c00000000000010000000000000000000000000000000002000000022000000000000000000000000,
  0x20000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000880000000000000000,
  0x20000000020000105f00000000000030310000000000000020000000000000002000000022000000230000000000000032,
  0x100000000000000010000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000,
  0x20000000000000100400000000000030000000000000000020000000000000002000000002000000000000000000000000,
  0x110000030000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0x20000000020000000400000000000010000000000000000020000000000000002000000022000000000000000000000000]

def valid (charged : Bool) (r c m : Nat) := table[9*charged.toNat+3*(r%3)+c%3]!.testBit m
def cnb (m : Nat) := bit m 5 + 2*bit m 7 + 4*bit m 3 + 8*bit m 1

private theorem localCheck : ∀ (r c : Fin 3) (m : Fin 512) (h : Bool),
    maskOK m →
    twoOrbitPatch 23 (6+(r.val:Int),6+(c.val:Int)) m = (if h then full else 0) →
    ∀ o : Fin 5, starOK 23 (7+(r.val:Int),7+(c.val:Int)) (bit m 4) (cnb m) o →
    twoOrbitStar 23 (7+(r.val:Int),7+(c.val:Int)) (bit m 4) (cnb m) o=0 →
    valid h r c m := by native_decide

abbrev Site := Fin 5 × Fin 5
def mid : Site := (2,2)
def shiftSite (p : Site) (d : Fin 4) : Option Site :=
  let q := shift ((p.1.val:Int),(p.2.val:Int)) d
  if h : 0≤q.1 ∧ q.1<5 ∧ 0≤q.2 ∧ q.2<5 then
    some (⟨q.1.toNat,by omega⟩,⟨q.2.toNat,by omega⟩) else none
def opp (d : Fin 4) := (d.val+2)%4
abbrev Domain := Array (Array (List Nat))
-- Materialize each pass, avoiding the exponential cost of inlining the
-- preceding pass in each neighboring lookup.
def cache (f : Site → List Nat) : Domain :=
  Array.ofFn (fun i : Fin 5 => Array.ofFn fun j : Fin 5 => f (i,j))
def get (D : Domain) (p : Site) := (D[p.1.val]!)[p.2.val]!
private theorem cached (f : Site → List Nat) (p : Site) : get (cache f) p=f p := by
  simp [cache,get]
def strips := Array.ofFn (fun m : Fin 512 => Array.ofFn fun d : Fin 4 => overlapBits m d)
def ov (m : Nat) (d : Nat) := (strips[m]!)[d]!
private theorem ov_eq (m : Fin 512) (d : Nat) (hd : d<4) : ov m d=overlapBits m d := by
  simp [ov,strips,hd]

def base (r c : Nat) : Domain := cache fun p => (List.range 512).filter fun m =>
  valid (p==mid) (r+p.1.val) (c+p.2.val) m
def pass (D : Domain) : Domain := cache fun p => (get D p).filter fun m =>
  decide (∀ d : Fin 4, (match shiftSite p d with
    | none => true
    | some q => (get D q).any (fun z => ov z (opp d) == ov m d))=true)
def passes (r c : Nat) : Nat → Domain
  | 0 => base r c
  | i+1 => pass (passes r c i)

def singletonCorner (m : Nat) := m==1 || m==4 || m==64 || m==256
private theorem filtered : ∀ r c : Fin 3,
    (get (passes r c 12) mid).all (fun m => (r.val+2)%3==1 && (c.val+2)%3==1 && singletonCorner m) := by
  native_decide

theorem prune_sound (r c : Fin 3) (M : Site → Fin 512)
    (baseOK : ∀ p, valid (p==mid) (r.val+p.1.val) (c.val+p.2.val) (M p))
    (meet : ∀ p d q, shiftSite p d=some q → overlapBits (M q) (opp d)=overlapBits (M p) d) :
    (r.val+2)%3=1 ∧ (c.val+2)%3=1 ∧ singletonCorner (M mid) := by
  have kept (n : Nat) (p : Site) : (M p).val ∈ get (passes r c n) p := by
    induction n generalizing p with
    | zero => simp [passes,base,cached,baseOK]
    | succ n ih =>
      rw [passes,pass,cached]
      apply List.mem_filter.mpr
      refine ⟨ih _,decide_eq_true ?_⟩
      intro d
      cases eq : shiftSite p d with
      | none => trivial
      | some q => exact List.any_eq_true.mpr ⟨_,ih q,by
          rw [ov_eq (M q) (opp d) (Nat.mod_lt _ (by decide : 0<4)),ov_eq _ _ d.isLt,meet p d q eq]; simp⟩
  have h := List.all_eq_true.mp (filtered r c) _ (kept 12 mid)
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

theorem packed_center {n : Nat} (F : Finset (GridVertex n n))
    (a : origins n) (v : GridVertex n n) (eq : coord v=coord a+(1,1)) :
    bit (maskAt F a) 4=(decide (v∈F)).toNat ∧ cnb (maskAt F a)=neighbours F (coord v) := by
  have bits (q : Fin 9) := patch_bit F a.1.val a.2.val (by have := a.1.isLt; omega)
    (by have := a.2.isLt; omega) q
  change ∀ (q : Fin 9), bit (maskAt F a) q=(marked F (coord a+offset q)).toNat at bits
  constructor
  · exact (bits ⟨4,by decide⟩).trans (by rw [← marked_at F v,eq]; rfl)
  · have extract (d : Fin 4) (q : Fin 9) (e : shift (coord a+(1,1)) d=coord a+offset q) :
        bit (neighbours F (coord v)) d=bit (maskAt F a) q := by
      rw [neighbours_bit,bits,eq,e]
    have pack : ∀ b : Fin 16, b.val=bit b 0+2*bit b 1+4*bit b 2+8*bit b 3 := by decide +kernel
    refine Eq.trans ?_ (pack ⟨neighbours F (coord v),code_lt _⟩).symm
    change cnb _=bit (neighbours F (coord v)) 0+2*_+4*_+8*_
    exact (by
      unfold cnb
      rw [extract ⟨0,by decide⟩ ⟨5,by decide⟩ (by ext <;> simp [shift,offset] <;> ring),
        extract ⟨1,by decide⟩ ⟨7,by decide⟩ (by ext <;> simp [shift,offset] <;> ring),
        extract ⟨2,by decide⟩ ⟨3,by decide⟩ (by ext <;> simp [shift,offset]),
        extract ⟨3,by decide⟩ ⟨1,by decide⟩ (by ext <;> simp [shift,offset])])

theorem physical_atom {u r c : Nat} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (hr : 6≤r ∧ r+7≤33+42*u) (hc : 6≤c ∧ c+7≤33+42*u)
    (h : Bool) (z : ∀ v, starSlack F P v=0)
    (a : origins (35+42*u)) (ar : a.1.val=r) (ac : a.2.val=c)
    (w : patchSlack F a=if h then full else 0) :
    valid h r c (maskAt F a) := by
  let n := 35+42*u
  let v : GridVertex n n := (⟨r+1,by dsimp [n]; omega⟩,⟨c+1,by dsimp [n]; omega⟩)
  have xy : coord v=coord a+(1,1) := by ext <;> simp [v,coord,ar,ac]
  obtain ⟨mark,neigh⟩ := packed_center F a v xy
  let m := maskAt F a
  let o : Fin 5 := ⟨outDir v (P v),outDir_lt ..⟩
  have s := z v
  unfold starSlack at s
  rw [←mark,←neigh] at s
  have ok := starOK_physical F acy v _ (fun hp => step _ hp.symm)
  rw [←mark,←neigh] at ok
  let t := 4+14*(u:Int)
  have ns : (n:Int)=23+3*t := by dsimp [n,t]; push_cast; ring
  have na : (n:Int)-2=21+3*t := by rw [ns]; ring
  have loc := starLocation_transport (b:=23) (by decide) (j:=t) (by dsimp [t]; positivity) (coord v)
  have patch := patchLocation_transport (b:=21) (by decide) (j:=t) (by dsimp [t]; positivity) (coord a)
  have aa : representative 21 t (coord a)=((6:Int)+(r%3:Nat),(6:Int)+(c%3:Nat)) := by
    ext <;> simp [representative,rep,coord,ar,ac,t] <;> split_ifs <;> omega
  -- At residue two the center wraps from representative 8 to 6 rather than 9.
  let pos (b : Nat) := (6:Int)+((b+1)%3:Nat)
  have vv : representative 23 t (coord v)=(pos r,pos c) := by
    ext <;> simp [representative,rep,coord,v,t,pos] <;> split_ifs <;> omega
  have ok' : starOK 23 (7+(r%3:Int),7+(c%3:Int)) (bit m 4) (cnb m) o := by
    have inside' (d : Nat) : inside 23 (shift (7+(r%3:Int),7+(c%3:Int)) d) := by
      unfold shift; split <;> simp [inside] <;> omega
    unfold starOK at ok ⊢
    simp only [inside',Bool.true_and] at *
    simp only [Bool.and_eq_true,Bool.or_eq_true,List.all_eq_true,Bool.true_and] at *
    exact ⟨fun d hd => (ok.1 _ hd).imp_right And.right,ok.2.imp_right And.right⟩
  have sa : twoOrbitStar 23 (pos r,pos c) (bit m 4) (cnb m) o=0 := by
    change twoOrbitStar (n:Int) _ _ _ _=0 at s
    simpa only [twoOrbitStar,ns,loc,vv] using s
  have coincide : ∀ i j : Fin 3, ∀ f : Fin 2, ∀ b : Fin 16, ∀ out : Fin 5,
      twoOrbitStar 23 ((6:Int)+((i.val+1)%3:Nat),(6:Int)+((j.val+1)%3:Nat)) f b out =
      twoOrbitStar 23 (7+(i.val:Int),7+(j.val:Int)) f b out := by native_decide
  let i : Fin 3 := ⟨r%3,by omega⟩
  let j : Fin 3 := ⟨c%3,by omega⟩
  have bnd : cnb m <16 := by unfold cnb bit; omega
  have same := coincide i j ⟨bit m 4,by unfold bit; omega⟩ ⟨cnb m,bnd⟩ o
  have modr : (r+1)%3=(i.val+1)%3 := by dsimp [i]; omega
  have modc : (c+1)%3=(j.val+1)%3 := by dsimp [j]; omega
  dsimp only [pos] at sa; rw [modr,modc] at sa
  have wa : twoOrbitPatch 23 ((6:Int)+(r%3:Nat),(6:Int)+(c%3:Nat)) m=if h then full else 0 := by
    change twoOrbitPatch (n:Int) _ _=_ at w
    simpa only [twoOrbitPatch,na,patch,aa,show (23:Int)-2=21 by decide] using w
  have check := localCheck i j m h (physical_mask_ok F acy ..) wa o
    (by simpa [i,j,Int.natCast_mod] using ok') (same ▸ sa)
  simpa [valid,i,j] using check

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.PatchFilter
