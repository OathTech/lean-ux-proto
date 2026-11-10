import C1BelowCoverMachine
import AllowedipsStackReady
import PairServiceCall
import AllowedipsPlacementPrefix
import StackFrame

/-! Result C1, work package 3, covering path: the machine from the comparison
at `add+0x267` to the common exit `add+0x549`, with its coverage calls. The
two sub-cases (below a parent, at the root) share the first half. Memory is
described against `mid`, the memory after the first coverage call. -/
namespace Binary.Pair.Allowedips.C1Cover
open AllowedipsMutationImage TrustBase AllowedipsChild Placement Binary.CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-- What a coverage call from stack pointer `stack` may write. -/
def CallWrites (stack : UInt64) (c : Context) (a : BitVec 64) : Prop :=
  InRange (stack.toBitVec-8) 8 a ∨ c.writes a

/-- The separations the path uses: the node below, the fresh node and a
third region (`other`: the parent node, or the root slot) are pairwise
apart; `add`'s 48 bytes of locals, the coverage call's writes and the
coverage state are apart from all three, and the call's writes and the
coverage state from the locals. -/
structure Apart (c : Context) (stack : UInt64) (down base : BitVec 64) (other : BitVec 64 → Prop) : Prop where
  downBase : ∀ a, InRange down 72 a → ¬InRange base 72 a
  downOther : ∀ a, InRange down 72 a → ¬other a
  baseOther : ∀ a, InRange base 72 a → ¬other a
  locals : ∀ a, InRange stack.toBitVec 48 a → ¬(InRange down 72 a ∨ InRange base 72 a ∨ other a)
  call : ∀ a, CallWrites stack c a →
    ¬(InRange stack.toBitVec 48 a ∨ InRange down 72 a ∨ InRange base 72 a ∨ other a)
  context : ∀ a, c.bytes a →
    ¬(InRange stack.toBitVec 48 a ∨ InRange down 72 a ∨ InRange base 72 a ∨ other a)

theorem off_in (p : BitVec 64) (size off len : Nat) (h : off+len ≤ size) (a : BitVec 64)
    (inside : InRange (p + .ofNat 64 off) len a) : InRange p size a := by
  obtain ⟨i,hi,rfl⟩ := inside
  exact ⟨off+i,by omega,by rw [BitVec.add_assoc,←BitVec.ofNat_add]⟩

theorem zero_in (p : BitVec 64) (size len : Nat) (h : len ≤ size) (a : BitVec 64)
    (inside : InRange p len a) : InRange p size a := by
  obtain ⟨i,hi,rfl⟩ := inside
  exact ⟨i,by omega,rfl⟩

theorem key_in (p : BitVec 64) (index : Nat) (bound : index<16) (a : BitVec 64)
    (inside : InRange (p+32+.ofNat 64 index) 1 a) : InRange p 72 a := by
  obtain ⟨i,hi,rfl⟩ := inside
  refine ⟨32+index+i,by omega,?_⟩
  simp only [BitVec.ofNat_add,BitVec.add_assoc]
  rfl

theorem off_apart (base : BitVec 64) (i ni j nj : Nat) (ibound : i+ni ≤ 2^64) (jbound : j+nj ≤ 2^64)
    (apart : i+ni ≤ j ∨ j+nj ≤ i) (k : Nat) (hk : k<ni) :
    ¬InRange (base + .ofNat 64 j) nj (base + .ofNat 64 i + .ofNat 64 k) :=
  InRange.offset_disjoint base i ni j nj ibound jbound apart _ ⟨k,hk,rfl⟩

theorem zero_apart (base : BitVec 64) (ni j nj : Nat) (jbound : j+nj ≤ 2^64) (apart : ni ≤ j)
    (k : Nat) (hk : k<ni) : ¬InRange (base + .ofNat 64 j) nj (base + .ofNat 64 k) :=
  InRange.offset_disjoint base k 1 j nj (by omega) jbound (by omega) _ ⟨0,by omega,by simp⟩

theorem slot_in (p : BitVec 64) (b : Nat) (bound : b<2) (a : BitVec 64)
    (inside : InRange (slot p b) 8 a) : InRange p 72 a :=
  off_in p 72 (8+8*b) 8 (by omega) a inside

theorem slot_mapped (m : Mem 64) (p : BitVec 64) (b : Nat) (bound : b < 2)
    (left : (m.loadInt (p + 8) 8).isSome = true) (right : (m.loadInt (p + 16) 8).isSome = true) :
    (m.loadInt (slot p b) 8).isSome = true := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact left
  · exact right

/-- The state after `choose_and_connect_node(newnode, down)`, at the test of
`parent`; `mid` is the memory after the first coverage call. -/
structure Linked (c : Context) (s : MachineData) (down base : BitVec 64) (bit : Nat)
    (mid : DataMem) (w : MachineState) : Prop where
  pc : w.pc=(if s.regs.rbx=0 then Add.entry+0x71d else Add.entry+0x5c0)
  rsp : w.data.regs.rsp=s.regs.rsp
  rbx : w.data.regs.rbx=s.regs.rbx
  ready : CallsReady c w.data
  midFrame : EqualOutside (fun a => InRange (s.regs.rsp.toBitVec+0x10) 8 a ∨ CallWrites s.regs.rsp c a) s.dmem mid
  mem : w.data.dmem=mem1 mid s.regs.rsp.toBitVec down base bit

theorem mem1_frame (m : DataMem) (stack down base : BitVec 64) (bit : Nat) (bound : bit<2) :
    EqualOutside (fun a => InRange stack 48 a ∨ InRange down 72 a ∨ InRange base 72 a) m
      (mem1 m stack down base bit) := by
  intro a outside
  unfold mem1
  exact ((storeInt_frame _ _ _ _ a (fun h => outside (.inr (.inl (off_in down 72 48 8 (by omega) a h))))).trans
    (storeInt_frame _ _ _ _ a (fun h => outside (.inl (zero_in stack 48 8 (by omega) a h))))).trans
    (storeInt_frame _ _ _ _ a (fun h => outside (.inr (.inr (slot_in base bit bound a h)))))

theorem mem1_mapped (m : DataMem) (stack down base : BitVec 64) (bit : Nat) :
    Pair.MappedLe m (mem1 m stack down base bit) :=
  fun _ _ h => storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ h))

/-- `+0x267 … +0x5c0/+0x71d`: the comparison (covering case), the save of
`newnode`, the coverage call, and `choose_and_connect_node(newnode, down)`. -/
theorem first_half (fetch : Int64 → Option Decoded) (agree : AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (c : Context) (s : MachineData)
    (cidr : BitVec 8) (down base : BitVec 64) (byteIndex : Nat) (word : BitVec 32) (byte : BitVec 8)
    (bit : Bool) (other : BitVec 64 → Prop)
    (apart : Apart c s.regs.rsp down base other) (ready : CallsReady c s)
    (cidrRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x10) 1=some cidr.toNat)
    (covers : cidr.toNat ≤ (s.regs.get (.low .r13 .W8)).toNat)
    (baseRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some base.toNat)
    (downRead : s.dmem.loadInt s.regs.rsp.toBitVec 8=some down.toNat)
    (indexBound : byteIndex<16)
    (indexRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x2b) 1=some (byteIndex : Int))
    (shiftRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x2c) 4=some word.toNat)
    (byteRead : s.dmem.loadInt (down+32+.ofNat 64 byteIndex) 1=some byte.toNat)
    (chosen : byte.getLsbD (word.toNat%32)=bit)
    (savedMapped : (s.dmem.loadInt (s.regs.rsp.toBitVec+0x10) 8).isSome=true)
    (parentMapped : (s.dmem.loadInt (down+48) 8).isSome=true)
    (leftMapped : (s.dmem.loadInt (base+8) 8).isSome=true)
    (rightMapped : (s.dmem.loadInt (base+16) 8).isSome=true) :
    Eventually (instructionStep fetch) (fun w => ∃ mid, Linked c s down base bit.toNat mid w)
      ⟨s,Add.entry+0x267⟩ := by
  have bitBound : bit.toNat<2 := by cases bit <;> decide
  have first := compare_step s cidr base cidrRead baseRead
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r267_layout.agreement agree.add) s _ first)
  rintro ⟨u,upc⟩ ⟨regsU,memU,pcU⟩
  simp only [covers,↓reduceIte] at pcU
  simp only at regsU memU
  subst pcU
  have saveLayout : LaidOut Add.fetch (Add.entry+0x56d) (Add.r56d.take 1) := by binary_layout
  have rspU : u.regs.rsp=s.regs.rsp := by rw [regsU]
  have second := save_step u (by rw [memU,rspU]; exact savedMapped)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (saveLayout.agreement agree.add) u _ second)
  rintro ⟨u2,pc2⟩ ⟨pcU2,regsU2,memU2⟩
  simp only at pcU2 regsU2 memU2
  subst pcU2
  rw [memU,rspU,regsU] at memU2
  simp only at memU2
  have rspU2 : u2.regs.rsp=s.regs.rsp := by rw [regsU2,rspU]
  have frameU2 : EqualOutside (InRange (s.regs.rsp.toBitVec+0x10) 8) s.dmem u2.dmem :=
    memU2 ▸ storeInt_frame _ _ _ _
  have readyU2 : CallsReady c u2 := ready.frame rspU2 frameU2
    (memU2 ▸ fun _ _ h => storeInt_defined _ _ _ _ _ _ h)
    (fun a read h => apart.context a read (.inl (off_in _ 48 16 8 (by omega) a h)))
  have here := agree.add _ _ (show Add.fetch (Add.entry+0x572)=some _ from rfl)
  apply eventually_trans (instructionStep fetch) _ _ _
    (Binary.Pair.Services.call fetch (Add.entry+0x572) "L_ffffffff810f31f0" .pc tracePc here c u2 readyU2)
  rintro v ⟨pcV,rspV,rbxV,_,_,_,_,_,readyV,frameV⟩
  rw [rspU2] at frameV rspV
  have rbxV : v.data.regs.rbx=s.regs.rbx := by rw [rbxV,regsU2,regsU]
  have midFrame : EqualOutside (fun a => InRange (s.regs.rsp.toBitVec+0x10) 8 a ∨ CallWrites s.regs.rsp c a)
      s.dmem v.data.dmem := frameU2.trans frameV
  -- reads that the save and the call leave alone
  have through (address : BitVec 64) (size : Nat)
      (touched : ∀ i<size, InRange s.regs.rsp.toBitVec 48 (address+.ofNat 64 i) ∨
        InRange down 72 (address+.ofNat 64 i) ∨ InRange base 72 (address+.ofNat 64 i) ∨
        other (address+.ofNat 64 i))
      (save : ∀ i<size, ¬InRange (s.regs.rsp.toBitVec+0x10) 8 (address+.ofNat 64 i)) :
      v.data.dmem.loadInt address size=s.dmem.loadInt address size :=
    (midFrame.loadInt address size (fun i hi h => h.elim (save i hi)
      (fun call => apart.call _ call (touched i hi)))).symm
  have locals (off size : Nat) (within : off+size ≤ 48) (i : Nat) (hi : i<size) :
      InRange s.regs.rsp.toBitVec 48 (s.regs.rsp.toBitVec+.ofNat 64 off+.ofNat 64 i) :=
    off_in _ 48 off size within _ ⟨i,hi,rfl⟩
  have downV : v.data.dmem.loadInt s.regs.rsp.toBitVec 8=some down.toNat :=
    (through _ 8 (fun i hi => .inl ⟨i,by omega,rfl⟩)
      (fun i hi => zero_apart _ 8 16 8 (by omega) (by omega) i hi)).trans downRead
  have indexV : v.data.dmem.loadInt (s.regs.rsp.toBitVec+0x2b) 1=some (byteIndex : Int) :=
    (through _ 1 (fun i hi => .inl (locals 43 1 (by omega) i hi))
      (fun i hi => off_apart _ 43 1 16 8 (by omega) (by omega) (by omega) i hi)).trans indexRead
  have shiftV : v.data.dmem.loadInt (s.regs.rsp.toBitVec+0x2c) 4=some word.toNat :=
    (through _ 4 (fun i hi => .inl (locals 44 4 (by omega) i hi))
      (fun i hi => off_apart _ 44 4 16 8 (by omega) (by omega) (by omega) i hi)).trans shiftRead
  have baseV : v.data.dmem.loadInt (s.regs.rsp.toBitVec+0x10) 8=some base.toNat := by
    rw [←frameV.loadInt (s.regs.rsp.toBitVec+0x10) 8
      (fun i hi call => apart.call _ call (.inl (locals 16 8 (by omega) i hi))),memU2]
    exact load64_store _ _ base
  have inDown (address : BitVec 64) (size : Nat) (inside : ∀ i<size, InRange down 72 (address+.ofNat 64 i)) :
      v.data.dmem.loadInt address size=s.dmem.loadInt address size :=
    through address size (fun i hi => .inr (.inl (inside i hi)))
      (fun i hi h => apart.locals _ (off_in _ 48 16 8 (by omega) _ h) (.inl (inside i hi)))
  have inBase (address : BitVec 64) (size : Nat) (inside : ∀ i<size, InRange base 72 (address+.ofNat 64 i)) :
      v.data.dmem.loadInt address size=s.dmem.loadInt address size :=
    through address size (fun i hi => .inr (.inr (.inl (inside i hi))))
      (fun i hi h => apart.locals _ (off_in _ 48 16 8 (by omega) _ h) (.inr (.inl (inside i hi))))
  have byteV : v.data.dmem.loadInt (down+32+.ofNat 64 byteIndex) 1=some byte.toNat :=
    (inDown _ 1 (fun i hi => key_in down byteIndex indexBound _ ⟨i,hi,rfl⟩)).trans byteRead
  have parentV : (v.data.dmem.loadInt (down+48) 8).isSome=true := by
    rw [inDown (down+48) 8 (fun i hi => off_in down 72 48 8 (by omega) _ ⟨i,hi,rfl⟩)]; exact parentMapped
  have leftV : (v.data.dmem.loadInt (base+8) 8).isSome=true := by
    rw [inBase (base+8) 8 (fun i hi => off_in base 72 8 8 (by omega) _ ⟨i,hi,rfl⟩)]; exact leftMapped
  have rightV : (v.data.dmem.loadInt (base+16) 8).isSome=true := by
    rw [inBase (base+16) 8 (fun i hi => off_in base 72 16 8 (by omega) _ ⟨i,hi,rfl⟩)]; exact rightMapped
  have stackV : (v.data.dmem.loadInt s.regs.rsp.toBitVec 8).isSome=true := by rw [downV]; rfl
  have third := choose_step v.data down base byteIndex word byte bit indexBound
    (by rw [rspV]; exact downV) (by rw [rspV]; exact indexV) (by rw [rspV]; exact shiftV)
    (by rw [rspV]; exact baseV) byteV chosen
  rw [at_pc v _ (pcV.trans (by rfl : Add.entry+0x572+5=Add.entry+0x577))]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r577_layout.agreement agree.add) v.data _ third)
  rintro ⟨w1,pcw1⟩ ⟨pcW1,memW1,regsW1⟩
  simp only at pcW1 memW1 regsW1
  subst pcW1
  have r8W1 : w1.regs.r8=.ofBitVec base := by rw [regsW1]
  have rsiW1 : w1.regs.rsi=.ofBitVec down := by rw [regsW1]
  have rspW1 : w1.regs.rsp=s.regs.rsp := by rw [regsW1]; exact rspV
  have rbxW1 : w1.regs.rbx=s.regs.rbx := by rw [regsW1]; exact rbxV
  have fourth := link_step w1 bit.toNat bitBound (by rw [regsW1]) (by rw [regsW1])
    (by rw [memW1,rsiW1]; exact parentV)
    (by rw [memW1,rsiW1,rspW1]; exact storeInt_defined _ _ _ _ _ _ stackV)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r597_layout.agreement agree.add) w1 _ fourth)
  rintro ⟨w2,pcw2⟩ ⟨pcW2,memW2,regsW2⟩
  simp only at pcW2 memW2 regsW2
  subst pcW2
  rw [memW1,rsiW1,r8W1,rspW1] at memW2
  have r8W2 : w2.regs.r8=.ofBitVec base := by rw [regsW2]; exact r8W1
  have rsiW2 : w2.regs.rsi=.ofBitVec down := by rw [regsW2]; exact rsiW1
  have rspW2 : w2.regs.rsp=s.regs.rsp := by rw [regsW2]; exact rspW1
  have rbxW2 : w2.regs.rbx=s.regs.rbx := by rw [regsW2]; exact rbxW1
  have fifth := slot_step w2 bit.toNat bitBound (by rw [regsW2])
    (by rw [memW2,r8W2]
        exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _
          (slot_mapped _ _ _ bitBound leftV rightV)))
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r5b2_layout.agreement agree.add) w2 _ fifth)
  rintro ⟨w3,pcw3⟩ ⟨pcW3,memW3,regsW3⟩
  simp only at pcW3 memW3 regsW3
  rw [memW2,r8W2,rsiW2] at memW3
  have rspW : w3.regs.rsp=s.regs.rsp := by rw [regsW3]; exact rspW2
  have rbxW : w3.regs.rbx=s.regs.rbx := by rw [regsW3]; exact rbxW2
  have memEq : w3.dmem=mem1 v.data.dmem s.regs.rsp.toBitVec down base bit.toNat := memW3
  refine ⟨v.data.dmem,⟨?_,rspW,rbxW,?_,midFrame,memEq⟩⟩
  · rw [pcW3,rbxW2]
  · have frame : EqualOutside (fun a => InRange s.regs.rsp.toBitVec 48 a ∨ InRange down 72 a ∨
        InRange base 72 a) v.data.dmem w3.dmem := by
      rw [memEq]; exact mem1_frame _ _ _ _ _ bitBound
    have mapped : Pair.MappedLe v.data.dmem w3.dmem := by
      rw [memEq]; exact mem1_mapped _ _ _ _ _
    exact readyV.frame (rspW.trans rspV.symm) frame mapped
      (fun a read h => apart.context a read
        (h.elim .inl (fun h => .inr (h.elim .inl (fun h => .inr (.inl h))))))

#print axioms first_half

/-- Everything written between `+0x267` and the second coverage call's return. -/
def HalfWrites (s : MachineData) (c : Context) (down base : BitVec 64) (bit : Nat) (a : BitVec 64) : Prop :=
  InRange (s.regs.rsp.toBitVec+0x10) 8 a ∨ InRange s.regs.rsp.toBitVec 8 a ∨ InRange (down+48) 8 a ∨
    InRange (slot base bit) 8 a ∨ CallWrites s.regs.rsp c a

theorem mem1_fine (m : DataMem) (stack down base : BitVec 64) (bit : Nat) :
    EqualOutside (fun a => InRange stack 8 a ∨ InRange (down+48) 8 a ∨ InRange (slot base bit) 8 a) m
      (mem1 m stack down base bit) := by
  intro a outside
  unfold mem1
  exact ((storeInt_frame _ _ _ _ a (fun h => outside (.inr (.inl h)))).trans
    (storeInt_frame _ _ _ _ a (fun h => outside (.inl h)))).trans
    (storeInt_frame _ _ _ _ a (fun h => outside (.inr (.inr h))))

/-- The two connection stores of `choose_and_connect_node(newnode, down)`
without the stack save between them. -/
def link1 (m : DataMem) (down base : BitVec 64) (bit : Nat) : DataMem :=
  (m.storeInt (down+48) 8 (packed base bit).toInt).storeInt (slot base bit) 8 down.toInt

theorem link1_mem1 (m : DataMem) (stack down base : BitVec 64) (bit : Nat) :
    EqualOutside (InRange stack 8) (link1 m down base bit) (mem1 m stack down base bit) :=
  (storeInt_frame _ stack 8 base.toInt).storeInt _ _ _

/-- The second coverage call's return, on either sub-case: what the
remaining instructions read is as at `+0x267`. -/
structure Returned2 (c : Context) (s : MachineData) (down base : BitVec 64) (bit : Nat)
    (mid : DataMem) (x : MachineState) : Prop where
  rsp : x.data.regs.rsp=s.regs.rsp
  rbx : x.data.regs.rbx=s.regs.rbx
  ready : CallsReady c x.data
  frame : EqualOutside (HalfWrites s c down base bit) s.dmem x.data.dmem
  ideal : EqualOutside (fun a => InRange s.regs.rsp.toBitVec 8 a ∨ CallWrites s.regs.rsp c a)
    (link1 mid down base bit) x.data.dmem
  saved : x.data.dmem.loadInt s.regs.rsp.toBitVec 8=some base.toNat

theorem second_call (fetch : Int64 → Option Decoded) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (down base : BitVec 64) (bit : Nat) (other : BitVec 64 → Prop) (mid : DataMem)
    (w : MachineState) (pc : Int64)
    (here : fetch pc=some ⟨Instrumentation.callInstruction "L_ffffffff810f31f0",5⟩)
    (apart : Apart c s.regs.rsp down base other) (bitBound : bit<2)
    (linked : Linked c s down base bit mid w) (at_ : w.pc=pc) :
    Eventually (instructionStep fetch) (fun x => x.pc=pc+5 ∧ Returned2 c s down base bit mid x) w := by
  rw [at_pc w _ at_]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Binary.Pair.Services.call fetch pc "L_ffffffff810f31f0" .pc tracePc here c w.data linked.ready)
  rintro x ⟨pcX,rspX,rbxX,_,_,_,_,_,readyX,frameX⟩
  rw [linked.rsp] at frameX rspX
  have fine := mem1_fine mid s.regs.rsp.toBitVec down base bit
  rw [←linked.mem] at fine
  have ideal := (link1_mem1 mid s.regs.rsp.toBitVec down base bit).trans (linked.mem ▸ frameX)
  refine ⟨pcX,rspX,rbxX.trans linked.rbx,readyX,?_,ideal,?_⟩
  · intro a outside
    exact ((linked.midFrame a (fun h => outside (h.elim .inl (fun h => .inr (.inr (.inr (.inr h))))))).trans
      (fine a (fun h => outside (h.elim (fun h => .inr (.inl h))
        (fun h => .inr (.inr (h.elim .inl (fun h => .inr (.inl h))))))))).trans
      (frameX a (fun h => outside (.inr (.inr (.inr (.inr h))))))
  · rw [←frameX.loadInt s.regs.rsp.toBitVec 8
      (fun i hi call => apart.call _ call (.inl ⟨i,by omega,rfl⟩)),linked.mem]
    unfold mem1
    rw [←(storeInt_frame _ (slot base bit) 8 down.toInt).loadInt s.regs.rsp.toBitVec 8
      (fun i hi h => apart.locals _ ⟨i,by omega,rfl⟩ (.inr (.inl (slot_in base bit bitBound _ h))))]
    exact load64_store _ _ base

#print axioms second_call

/-- The memory the data side reasons about, below a parent: the four
connection stores on `mid`. -/
def coverParent (m : DataMem) (down base parent : BitVec 64) (bit bit2 : Nat) : DataMem :=
  ((link1 m down base bit).storeInt (base+48) 8 (packed parent bit2).toInt).storeInt
    (slot parent bit2) 8 base.toInt

/-- The same at the root: the fresh node's parent word is the root slot's
address tagged 2, and the slot holds the fresh node. -/
def coverRoot (m : DataMem) (down base rootSlot : BitVec 64) (bit : Nat) : DataMem :=
  ((link1 m down base bit).storeInt (base+48) 8 (rootSlot ||| 2#64).toInt).storeInt rootSlot 8 base.toInt

def PathWrites (s : MachineData) (c : Context) (down base : BitVec 64) (other : BitVec 64 → Prop)
    (a : BitVec 64) : Prop :=
  InRange s.regs.rsp.toBitVec 48 a ∨ InRange down 72 a ∨ InRange base 72 a ∨ other a ∨
    CallWrites s.regs.rsp c a

/-- The common exit: `ebx = 0`, the stack pointer of `+0x267`, and memory
equal to `ideal` except in the saved stack word and the coverage calls'
writes. -/
structure Done (c : Context) (s : MachineData) (down base : BitVec 64) (other : BitVec 64 → Prop)
    (mid ideal : DataMem) (t : MachineState) : Prop where
  pc : t.pc=Add.entry+0x549
  rbx : t.data.regs.rbx=0
  rsp : t.data.regs.rsp=s.regs.rsp
  ready : CallsReady c t.data
  midFrame : EqualOutside (fun a => InRange (s.regs.rsp.toBitVec+0x10) 8 a ∨ CallWrites s.regs.rsp c a) s.dmem mid
  ideal : EqualOutside (fun a => InRange s.regs.rsp.toBitVec 8 a ∨ CallWrites s.regs.rsp c a) ideal t.data.dmem
  frame : EqualOutside (PathWrites s c down base other) s.dmem t.data.dmem

theorem half_path {s : MachineData} {c : Context} {down base : BitVec 64} {bit : Nat}
    {other : BitVec 64 → Prop} (bitBound : bit<2) {a : BitVec 64}
    (written : HalfWrites s c down base bit a) : PathWrites s c down base other a := by
  rcases written with h|h|h|h|h
  · exact .inl (off_in _ 48 16 8 (by omega) a h)
  · exact .inl (zero_in _ 48 8 (by omega) a h)
  · exact .inr (.inl (off_in down 72 48 8 (by omega) a h))
  · exact .inr (.inr (.inl (slot_in base bit bitBound a h)))
  · exact .inr (.inr (.inr (.inr h)))

theorem key_slot_apart (base : BitVec 64) (index bit : Nat) (indexBound : index<16) (bitBound : bit<2)
    (a : BitVec 64) (inside : InRange (base+32+.ofNat 64 index) 1 a) : ¬InRange (slot base bit) 8 a := by
  have address : base+32+.ofNat 64 index=base+.ofNat 64 (32+index) := by
    simp only [BitVec.ofNat_add,BitVec.add_assoc]; rfl
  rw [address] at inside
  exact InRange.offset_disjoint base (32+index) 1 (8+8*bit) 8 (by omega) (by omega) (by omega) a inside

theorem parent_slot_apart (base : BitVec 64) (bit : Nat) (bitBound : bit<2)
    (a : BitVec 64) (inside : InRange (base+48) 8 a) : ¬InRange (slot base bit) 8 a :=
  InRange.offset_disjoint base 48 8 (8+8*bit) 8 (by omega) (by omega) (by omega) a inside

section Reads
variable {c : Context} {s : MachineData} {down base : BitVec 64} {bit : Nat} {other : BitVec 64 → Prop}
  {mid : DataMem} {x : MachineState}

theorem Returned2.third (ret : Returned2 c s down base bit mid x) (apart : Apart c s.regs.rsp down base other)
    (bitBound : bit<2) (address : BitVec 64) (size : Nat)
    (inside : ∀ i<size, other (address+.ofNat 64 i)) :
    x.data.dmem.loadInt address size=s.dmem.loadInt address size := by
  refine (ret.frame.loadInt address size ?_).symm
  rintro i hi (h|h|h|h|h)
  · exact apart.locals _ (off_in _ 48 16 8 (by omega) _ h) (.inr (.inr (inside i hi)))
  · exact apart.locals _ (zero_in _ 48 8 (by omega) _ h) (.inr (.inr (inside i hi)))
  · exact apart.downOther _ (off_in down 72 48 8 (by omega) _ h) (inside i hi)
  · exact apart.baseOther _ (slot_in base bit bitBound _ h) (inside i hi)
  · exact apart.call _ h (.inr (.inr (.inr (inside i hi))))

theorem Returned2.fresh (ret : Returned2 c s down base bit mid x) (apart : Apart c s.regs.rsp down base other)
    (address : BitVec 64) (size : Nat)
    (inside : ∀ i<size, InRange base 72 (address+.ofNat 64 i))
    (slotApart : ∀ i<size, ¬InRange (slot base bit) 8 (address+.ofNat 64 i)) :
    x.data.dmem.loadInt address size=s.dmem.loadInt address size := by
  refine (ret.frame.loadInt address size ?_).symm
  rintro i hi (h|h|h|h|h)
  · exact apart.locals _ (off_in _ 48 16 8 (by omega) _ h) (.inr (.inl (inside i hi)))
  · exact apart.locals _ (zero_in _ 48 8 (by omega) _ h) (.inr (.inl (inside i hi)))
  · exact apart.downBase _ (off_in down 72 48 8 (by omega) _ h) (inside i hi)
  · exact slotApart i hi h
  · exact apart.call _ h (.inr (.inr (.inl (inside i hi))))

end Reads

/-- `+0x5c0 … +0x549` below a parent: the coverage call,
`choose_and_connect_node(parent, newnode)`, `ebx := 0`. -/
theorem parent_half (fetch : Int64 → Option Decoded) (agree : AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (c : Context) (s : MachineData)
    (down base : BitVec 64) (bit : Nat) (mid : DataMem) (w : MachineState)
    (index shift byte : Nat)
    (apart : Apart c s.regs.rsp down base (InRange s.regs.rbx.toBitVec 72)) (bitBound : bit<2)
    (linked : Linked c s down base bit mid w) (parent : s.regs.rbx≠0)
    (indexBound : index<16) (shiftBound : shift<8) (byteBound : byte<256)
    (indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec+25) 1=some (index : Int))
    (shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec+26) 1=some (shift : Int))
    (byteRead : s.dmem.loadInt (base+32+.ofNat 64 index) 1=some (byte : Int))
    (nodeMapped : (s.dmem.loadInt (base+48) 8).isSome=true)
    (leftMapped : (s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8).isSome=true)
    (rightMapped : (s.dmem.loadInt (s.regs.rbx.toBitVec+16) 8).isSome=true) :
    Eventually (instructionStep fetch) (Done c s down base (InRange s.regs.rbx.toBitVec 72) mid
      (coverParent mid down base s.regs.rbx.toBitVec bit (selected byte shift))) w := by
  have here := agree.add _ _ (show Add.fetch (Add.entry+0x5c0)=some _ from rfl)
  apply eventually_trans (instructionStep fetch) _ _ _
    (second_call fetch tracePc c s down base bit _ mid w (Add.entry+0x5c0) here apart bitBound linked
      (by rw [linked.pc]; simp only [parent,↓reduceIte]))
  rintro x ⟨pcX,ret⟩
  have selBound := Nat.mod_lt (byte/2^shift) (by decide : 0<2)
  change selected byte shift<2 at selBound
  have indexX : x.data.dmem.loadInt (x.data.regs.rbx.toBitVec+25) 1=some (index : Int) := by
    rw [ret.rbx,ret.third apart bitBound (s.regs.rbx.toBitVec+25) 1
      (fun i hi => off_in _ 72 25 1 (by omega) _ ⟨i,hi,rfl⟩)]
    exact indexRead
  have shiftX : x.data.dmem.loadInt (x.data.regs.rbx.toBitVec+26) 1=some (shift : Int) := by
    rw [ret.rbx,ret.third apart bitBound (s.regs.rbx.toBitVec+26) 1
      (fun i hi => off_in _ 72 26 1 (by omega) _ ⟨i,hi,rfl⟩)]
    exact shiftRead
  have byteX : x.data.dmem.loadInt (base+32+.ofNat 64 index) 1=some (byte : Int) := by
    rw [ret.fresh apart (base+32+.ofNat 64 index) 1
      (fun i hi => key_in base index indexBound _ ⟨i,hi,rfl⟩)
      (fun i hi => key_slot_apart base index bit indexBound bitBound _ ⟨i,hi,rfl⟩)]
    exact byteRead
  have nodeX : (x.data.dmem.loadInt (base+48) 8).isSome=true := by
    rw [ret.fresh apart (base+48) 8 (fun i hi => off_in base 72 48 8 (by omega) _ ⟨i,hi,rfl⟩)
      (fun i hi => parent_slot_apart base bit bitBound _ ⟨i,hi,rfl⟩)]
    exact nodeMapped
  have leftX : (x.data.dmem.loadInt (s.regs.rbx.toBitVec+8) 8).isSome=true := by
    rw [ret.third apart bitBound (s.regs.rbx.toBitVec+8) 8
      (fun i hi => off_in _ 72 8 8 (by omega) _ ⟨i,hi,rfl⟩)]
    exact leftMapped
  have rightX : (x.data.dmem.loadInt (s.regs.rbx.toBitVec+16) 8).isSome=true := by
    rw [ret.third apart bitBound (s.regs.rbx.toBitVec+16) 8
      (fun i hi => off_in _ 72 16 8 (by omega) _ ⟨i,hi,rfl⟩)]
    exact rightMapped
  have chosen := parent_choose_step x.data base index shift byte indexBound shiftBound byteBound
    indexX (by rw [ret.rsp]; exact ret.saved) shiftX byteX
  rw [at_pc x _ (pcX.trans (by rfl : Add.entry+0x5c0+5=Add.entry+0x5c5))]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r5c5_layout.agreement agree.add) x.data _ chosen)
  rintro ⟨y,pcy⟩ ⟨pcY,memY,regsY⟩
  simp only at pcY memY regsY
  subst pcY
  have r8Y : y.regs.r8=.ofBitVec base := by rw [regsY]
  have rbxY : y.regs.rbx=s.regs.rbx := by rw [regsY]; exact ret.rbx
  have rspY : y.regs.rsp=s.regs.rsp := by rw [regsY]; exact ret.rsp
  have layout : LaidOut Add.fetch (Add.entry+0x5e1) (Add.r5e1++Add.r5fc) := by binary_layout
  have linkedUp := parent_link_step y (selected byte shift) selBound (by rw [regsY]) (by rw [regsY])
    (by rw [memY,r8Y]; exact nodeX)
    (by rw [memY,r8Y,rbxY]
        exact storeInt_defined _ _ _ _ _ _ (slot_mapped _ _ _ selBound leftX rightX))
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (layout.agreement agree.add) y _ linkedUp)
  rintro ⟨t,pct⟩ ⟨pcT,memT,regsT⟩
  simp only at pcT memT regsT
  rw [memY,r8Y,rbxY] at memT
  have memEq : t.dmem=(x.data.dmem.storeInt (base+48) 8
      (packed s.regs.rbx.toBitVec (selected byte shift)).toInt).storeInt
      (slot s.regs.rbx.toBitVec (selected byte shift)) 8 base.toInt := memT
  have frame3 : EqualOutside (fun a => InRange (base+48) 8 a ∨
      InRange (slot s.regs.rbx.toBitVec (selected byte shift)) 8 a) x.data.dmem t.dmem := by
    rw [memEq]
    exact (storeInt_frame _ _ _ _).trans (storeInt_frame _ _ _ _)
  have rspT : t.regs.rsp=s.regs.rsp := by rw [regsT]; exact rspY
  refine ⟨pcT,by rw [regsT],rspT,?_,linked.midFrame,?_,?_⟩
  · exact ret.ready.frame (rspT.trans ret.rsp.symm) frame3
      (by rw [memEq]; exact fun _ _ h => storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ h))
      (fun a read h => apart.context a read (h.elim
        (fun h => .inr (.inr (.inl (off_in base 72 48 8 (by omega) a h))))
        (fun h => .inr (.inr (.inr (slot_in _ _ selBound a h))))))
  · rw [memEq]
    exact (ret.ideal.storeInt _ _ _).storeInt _ _ _
  · intro a outside
    exact (ret.frame a (fun h => outside (half_path bitBound h))).trans
      (frame3 a (fun h => outside (h.elim
        (fun h => .inr (.inr (.inl (off_in base 72 48 8 (by omega) a h))))
        (fun h => .inr (.inr (.inr (.inl (slot_in _ _ selBound a h))))))))

#print axioms parent_half

theorem above_apart (base : BitVec 64) (i ni nj : Nat) (ibound : i+ni ≤ 2^64) (apart : nj ≤ i)
    (k : Nat) (hk : k<ni) : ¬InRange base nj (base + .ofNat 64 i + .ofNat 64 k) := by
  rintro ⟨y,hy,e⟩
  exact InRange.offset_disjoint base i ni 0 nj ibound (by omega) (by omega) _ ⟨k,hk,rfl⟩
    ⟨y,hy,by simpa using e⟩

/-- `+0x71d … +0x549` at the root: the coverage call, the root slot's address
from the stack word at `rsp+8`, the fresh node's parent word and the slot. -/
theorem root_half (fetch : Int64 → Option Decoded) (agree : AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (c : Context) (s : MachineData)
    (down base rootSlot : BitVec 64) (bit : Nat) (mid : DataMem) (w : MachineState)
    (apart : Apart c s.regs.rsp down base (InRange rootSlot 8)) (bitBound : bit<2)
    (linked : Linked c s down base bit mid w) (root : s.regs.rbx=0)
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some rootSlot.toNat)
    (nodeMapped : (s.dmem.loadInt (base+48) 8).isSome=true)
    (slotMapped : (s.dmem.loadInt rootSlot 8).isSome=true) :
    Eventually (instructionStep fetch) (Done c s down base (InRange rootSlot 8) mid
      (coverRoot mid down base rootSlot bit)) w := by
  have here := agree.add _ _ (show Add.fetch (Add.entry+0x71d)=some _ from rfl)
  apply eventually_trans (instructionStep fetch) _ _ _
    (second_call fetch tracePc c s down base bit _ mid w (Add.entry+0x71d) here apart bitBound linked
      (by rw [linked.pc]; simp only [root,↓reduceIte]))
  rintro x ⟨pcX,ret⟩
  have slotX : x.data.dmem.loadInt (x.data.regs.rsp.toBitVec+8) 8=some rootSlot.toNat := by
    rw [ret.rsp,←slotRead]
    refine (ret.frame.loadInt (s.regs.rsp.toBitVec+8) 8 ?_).symm
    have locals (i : Nat) (hi : i<8) :
        InRange s.regs.rsp.toBitVec 48 (s.regs.rsp.toBitVec+8+.ofNat 64 i) :=
      off_in _ 48 8 8 (by omega) _ ⟨i,hi,rfl⟩
    rintro i hi (h|h|h|h|h)
    · exact off_apart _ 8 8 16 8 (by omega) (by omega) (by omega) i hi h
    · exact above_apart _ 8 8 8 (by omega) (by omega) i hi h
    · exact apart.locals _ (locals i hi) (.inl (off_in down 72 48 8 (by omega) _ h))
    · exact apart.locals _ (locals i hi) (.inr (.inl (slot_in base bit bitBound _ h)))
    · exact apart.call _ h (.inl (locals i hi))
  have nodeX : (x.data.dmem.loadInt (base+48) 8).isSome=true := by
    rw [ret.fresh apart (base+48) 8 (fun i hi => off_in base 72 48 8 (by omega) _ ⟨i,hi,rfl⟩)
      (fun i hi => parent_slot_apart base bit bitBound _ ⟨i,hi,rfl⟩)]
    exact nodeMapped
  have rootX : (x.data.dmem.loadInt rootSlot 8).isSome=true := by
    rw [ret.third apart bitBound rootSlot 8 (fun i hi => ⟨i,hi,rfl⟩)]
    exact slotMapped
  have published := root_step x.data rootSlot base slotX (by rw [ret.rsp]; exact ret.saved) nodeX
    (storeInt_defined _ _ _ _ _ _ rootX)
  rw [at_pc x _ (pcX.trans (by rfl : Add.entry+0x71d+5=Add.entry+0x722))]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r722_layout.agreement agree.add) x.data _ published)
  rintro ⟨t,pct⟩ ⟨pcT,memT,regsT⟩
  simp only at pcT memT regsT
  have frame3 : EqualOutside (fun a => InRange (base+48) 8 a ∨ InRange rootSlot 8 a) x.data.dmem t.dmem := by
    rw [memT]
    exact (storeInt_frame _ _ _ _).trans (storeInt_frame _ _ _ _)
  have rspT : t.regs.rsp=s.regs.rsp := by rw [regsT]; exact ret.rsp
  refine ⟨pcT,by rw [regsT],rspT,?_,linked.midFrame,?_,?_⟩
  · exact ret.ready.frame (rspT.trans ret.rsp.symm) frame3
      (by rw [memT]; exact fun _ _ h => storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ h))
      (fun a read h => apart.context a read (h.elim
        (fun h => .inr (.inr (.inl (off_in base 72 48 8 (by omega) a h))))
        (fun h => .inr (.inr (.inr h)))))
  · rw [memT]
    exact (ret.ideal.storeInt _ _ _).storeInt _ _ _
  · intro a outside
    exact (ret.frame a (fun h => outside (half_path bitBound h))).trans
      (frame3 a (fun h => outside (h.elim
        (fun h => .inr (.inr (.inl (off_in base 72 48 8 (by omega) a h))))
        (fun h => .inr (.inr (.inr (.inl h)))))))

#print axioms root_half
end Binary.Pair.Allowedips.C1Cover
