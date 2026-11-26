import GridGraphs.ResidueTwoUpper.OneGap.SouthCapWindow

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap

/-- Dense numbering of the catalogue's mark, four arrow and sheet
variables, in that order. -/
def wireNumber (r c t : Nat) := 6*(18*r+c)+t

def readWire (f : Nat → Nat → Nat → Bool) (n : Nat) :=
  f (n/6/18) (n/6%18) (n%6)

theorem read_wireNumber (f : Nat → Nat → Nat → Bool) (r c t : Nat)
    (hc : c<18) (ht : t<6) :
    readWire f (wireNumber r c t)=f r c t := by
  have a : wireNumber r c t / 6=18*r+c := by unfold wireNumber; omega
  have b : wireNumber r c t % 6=t := by unfold wireNumber; omega
  have d : (18*r+c)/18=r := by omega
  have e : (18*r+c)%18=c := by omega
  simp only [readWire,a,b,d,e]

/-- A slot with no board point has no mark, sheet or outgoing arrow. -/
def optionalSlot {h w r c : Nat} (i j : Nat) : Option (Slots h w r c) :=
  if hi : i<18 then if hj : j<18 then
    if inb : atlasSite h r i<119 ∧ atlasSite w c j<119 then
      some ⟨(⟨i,hi⟩,⟨j,hj⟩),inb⟩ else none
    else none
  else none

@[simp] theorem optionalSlot_val {h w r c : Nat} (x : Slots h w r c) :
    optionalSlot (h:=h) (w:=w) (r:=r) (c:=c) x.1.1.val x.1.2.val=some x := by
  simp [optionalSlot,x.1.1.isLt,x.1.2.isLt,x.2]

/-- Use signed offsets before clipping, so north/west of offset zero
do not alias a different slot by natural subtraction. -/
def nextSlot {h w r c : Nat} (x : Slots h w r c) (d : Nat) : Option (Slots h w r c) :=
  let z := ResidueZero.shift (x.1.1.val,x.1.2.val) d
  if 0≤z.1 ∧ 0≤z.2 then optionalSlot z.1.toNat z.2.toNat else none

def slotValue {h w r c : Nat} (W : WindowField (Slots h w r c)) (i j t : Nat) : Bool :=
  (optionalSlot i j).any fun x =>
    if t=0 then W.mark x else if t=5 then W.sheet x
    else (nextSlot x (t-1)).any (W.arrow x)

def numericField {h w r c : Nat} (W : WindowField (Slots h w r c)) : Nat → Bool :=
  readWire (slotValue W)

theorem numeric_mark {h w r c : Nat} (W : WindowField (Slots h w r c)) (x : Slots h w r c) :
    numericField W (wireNumber x.1.1.val x.1.2.val 0)=W.mark x := by
  rw [numericField,read_wireNumber _ _ _ _ x.1.2.isLt (by decide)]
  simp [slotValue]

theorem numeric_sheet {h w r c : Nat} (W : WindowField (Slots h w r c)) (x : Slots h w r c) :
    numericField W (wireNumber x.1.1.val x.1.2.val 5)=W.sheet x := by
  rw [numericField,read_wireNumber _ _ _ _ x.1.2.isLt (by decide)]
  simp [slotValue]

theorem numeric_arc {h w r c : Nat} (W : WindowField (Slots h w r c))
    (x : Slots h w r c) (d : Fin 4) :
    numericField W (wireNumber x.1.1.val x.1.2.val (d.val+1)) =
      (nextSlot x d.val).any (W.arrow x) := by
  have lt := d.isLt
  rw [numericField,read_wireNumber _ _ _ _ x.1.2.isLt (by omega)]
  simp [slotValue,show d.val+1≠5 by omega]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
