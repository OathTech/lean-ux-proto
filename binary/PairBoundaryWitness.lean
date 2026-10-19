import SourceAdapter
import PairBoundaryProof
import AllowedipsSourceWitness

namespace Binary.Pair.Trie.Witness
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Small synthetic positive headers, distinct from captured snapshots and
from the larger recorded-prefix executable suites. Both families return node 0. -/
def device (bits : Nat) : Device := {
  ifindex := 3, ifname := "wg0",
  peerAllowedips := {root4 := (if bits = 32 then some 0 else none), root6 := (if bits = 128 then some 0 else none)},
  nodes := ({} : Std.TreeMap NodeId AipNode).insert 0 (newNode 1 bits bits (some 0)),
  peers := ({} : Std.TreeMap PeerId Peer).insert 0 (AllowedipsWitness.peer 0) }

def world (bits : Nat) : World :=
  {AllowedipsWitness.world with wg := {AllowedipsWitness.world.wg with dev := some (device bits)}}

def names : Names := ⟨[(0,0xa00000)],[(0,0x600000)]⟩

def offsets : AllowedipsProbe.Offsets := ⟨72,0,8,24,25,26,27,32,1056⟩

def input : AllowedipsProbe.Input := {
  trace := .null, operation := 0, entry := AllowedipsImage.Lookup.entry.toBitVec.toNat,
  commonEntry := AllowedipsImage.CommonBits.entry.toBitVec.toNat,
  instructions := #[], labels := #[], hooks := #[], offsets,
  preempt := preemptCountAddress.toNat, entryPreempt := 0, budget := 100000 }

def coverage : CommonBitsCoverage.Context := ⟨⟨0x800000,0x900000,4,2,0⟩,512⟩

def words (bits : Nat) : List (Nat×Nat×Nat) :=
  [(0xa00000,8,0x600000),(0xa00008,8,0),(0xa00010,8,0),
   (0xa00018,1,bits),(0xa00019,1,bits/8 ^^^ ((bits/8-1)%8)),
   (0xa0001a,1,7-bits%8),(0xa0001b,1,bits),
   (0x600000+1056,4,1),(currentTaskAddress.toNat,8,0x800000),
   (preemptCountAddress.toNat,4,512),(0x8006e0,4,2),(0x8006e4,4,4),
   (0x8006e8,8,0x900000),(0x900000,8,0),
   (0x900008,8,0),(0x900010,8,0),(0x900018,8,0),(stackAddr-72,8,0xa00000)] ++
  (List.range 6).map (fun n => (stackAddr-80-(n+1)*8,8,0)) ++
  (if bits = 32 then [(0xa00020,4,1),(stackAddr-64,4,1)] else
    [(0xa00020,8,0),(0xa00028,8,1),(stackAddr-64,8,0),(stackAddr-56,8,1)])

def cells (bits : Nat) : List (BitVec 64 × UInt8) :=
  (words bits).flatMap fun (a,size,value) => (Int.toBytes size value).mapIdx (fun i b => (.ofNat 64 (a+i),b))

def cellMemory (bytes : List (BitVec 64 × UInt8)) : DataMem :=
  bytes.foldr (fun (a,b) m => m.insert a b) {}

def memory (bits : Nat) : DataMem := cellMemory (cells bits)

theorem cellMemory_read (bytes : List (BitVec 64 × UInt8)) (a : BitVec 64) :
    (cellMemory bytes)[a]? = ((bytes.find? (·.1 == a)).map Prod.snd) := by
  induction bytes with
  | nil => simp [cellMemory]
  | cons head tail ih =>
    simp only [cellMemory,List.foldr_cons,Std.ExtHashMap.getElem?_insert]
    change (if head.1 == a then some head.2 else (cellMemory tail)[a]?) = _
    rw [ih,List.find?_cons]
    cases h : head.1 == a <;> rfl

private theorem memory_load (bits : Nat) (a : BitVec 64) (size : Nat) :
    (memory bits).loadBytes a size =
      ((List.range size).map fun i => ((cells bits).find? (·.1 == a+.ofNat 64 i)).map Prod.snd).allSome := by
  simp only [Mem.loadBytes,Std.ExtHashMap.get?_eq_getElem?,memory,cellMemory_read]

def state (bits : Nat) : MachineState :=
  ⟨{regs := {rbx := 0xa00000,rbp := 0,rsp := .ofNat (stackAddr-80), r12 := .ofNat bits,r13 := .ofNat bits},dmem := memory bits},AllowedipsImage.Lookup.entry+0xd5⟩

private instance (x : Except String Unit) : Decidable (x = .ok ()) :=
  match x with
  | .error e => .isFalse (by intro h; cases h)
  | .ok () => .isTrue rfl

theorem check4 : initialBoundary names input coverage (state 32) (world 32) (some 0) 32 1 = .ok () := by
  simp only [initialBoundary,assertAt,callInput,locals,frameCheck,coverageCheck,coverageDataCheck,
    reconstruct,decodeNode,word,readNat,load64,load32,Mem.loadInt,state,memory_load]
  decide +kernel
theorem check6 : initialBoundary names input coverage (state 128) (world 128) (some 0) 128 1 = .ok () := by
  simp only [initialBoundary,assertAt,callInput,locals,frameCheck,coverageCheck,coverageDataCheck,
    reconstruct,decodeNode,word,readNat,load64,load32,Mem.loadInt,state,memory_load]
  decide +kernel

def Post (bits : Nat) (t : Executed) : Prop :=
  t.machine.pc = AllowedipsImage.Lookup.entry+0x101 ∧
  t.machine.data.regs.rbp.toBitVec = (.ofNat 64 0xa00000) ∧
  reconstruct names offsets t.machine.data.dmem = .ok (target (device bits)) ∧
  AllowedipsLoop.Frame (state bits).data coverage t.machine.data

theorem simulation (bits : Nat) (family : bits = 32 ∨ bits = 128)
    (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp1 : AllowedipsTraceCmp1Contract fetch) :
    Eventually (historyStep fetch) (Post bits) ⟨state bits,[state bits]⟩ := by
  have checked : initialBoundary names input coverage (state bits) (world bits) (some 0) bits 1 = .ok () := by
    rcases family with rfl | rfl
    · exact check4
    · exact check6
  obtain ⟨final,accepted,deviceAt⟩ : ∃ final,
      (Source.findNode (some 0) bits 1).run (world bits) = .ok (some 0,final) ∧
      final.wg.dev = some (device bits) := by
    have projected : ((Source.findNode (some 0) bits 1).run (world bits)).toOption.map Prod.fst = some (some 0) := by
      rcases family with rfl | rfl <;>
        (unfold Source.findNode Leanux.WG.findNode; simp only [Std.Legacy.Range.forIn_eq_forIn_range']; decide +kernel)
    cases executed : (Source.findNode (some 0) bits 1).run (world bits) with
    | error e => rw [executed] at projected; cases projected
    | ok result =>
      rw [executed] at projected
      have equal : result.1 = some 0 := Option.some.inj projected
      have accepted : (Source.findNode (some 0) bits 1).run (world bits) = .ok (some 0,result.2) := by
        simpa only [←equal] using executed
      have frame := (AllowedipsSource.findNode_accepted_select (some 0) bits 1 (world bits) result.2 (some 0) accepted).2
      exact ⟨result.2,by cases result; simp_all only [Except.ok.injEq,Prod.mk.injEq,and_true],by rw [frame]; rfl⟩
  have run := findNode_checked fetch decoder callbacks cmp1 names input coverage
    (state bits) (world bits) final (some 0) bits 1 (some 0) checked accepted
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨pc,answer,⟨d,atDevice,decoded⟩,frame⟩
  have equal : d = device bits := Option.some.inj (atDevice.symm.trans deviceAt)
  subst d
  exact ⟨pc,answer,decoded,frame⟩

theorem simulation4 (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp1 : AllowedipsTraceCmp1Contract fetch) :
    Eventually (historyStep fetch) (Post 32) ⟨state 32,[state 32]⟩ :=
  simulation 32 (.inl rfl) fetch decoder callbacks cmp1

theorem simulation6 (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp1 : AllowedipsTraceCmp1Contract fetch) :
    Eventually (historyStep fetch) (Post 128) ⟨state 128,[state 128]⟩ :=
  simulation 128 (.inr rfl) fetch decoder callbacks cmp1

#print axioms check4
#print axioms check6
#print axioms simulation4
#print axioms simulation6
end Binary.Pair.Trie.Witness
