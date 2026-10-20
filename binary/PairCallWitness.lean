import SourceAdapter
import PairCallAdequacy
import PairBoundaryWitness

namespace Binary.Pair.Trie.CallWitness
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def words (bits : Nat) : List (Nat×Nat×Nat) :=
  [(preemptCountAddress.toNat,4,0),(softirqPendingAddress.toNat,2,0),(stackAddr,8,stopAddr)] ++
  (List.range 18).map (fun i => (stackAddr-(i+1)*8,8,0)) ++
  (if bits = 32 then [(AllowedipsProbe.keyAddr,4,0x01000000)] else
    [(AllowedipsProbe.keyAddr,8,0),(AllowedipsProbe.keyAddr+8,8,0x0100000000000000)]) ++
  Witness.words bits

def cells (bits : Nat) : List (BitVec 64 × UInt8) :=
  (words bits).flatMap fun (a,size,value) => (Int.toBytes size value).mapIdx (fun i b => (.ofNat 64 (a+i),b))

def memory (bits : Nat) : DataMem := Witness.cellMemory (cells bits)

theorem memory_load (bits : Nat) (a : BitVec 64) (size : Nat) :
    (memory bits).loadBytes a size =
      ((List.range size).map fun i => ((cells bits).find? (·.1 == a+.ofNat 64 i)).map Prod.snd).allSome := by
  simp only [Mem.loadBytes,Std.ExtHashMap.get?_eq_getElem?,memory,Witness.cellMemory_read]

def state (bits : Nat) : MachineState :=
  ⟨{regs := {rdi := 0xa00000,rsi := .ofNat bits,rdx := .ofNat AllowedipsProbe.keyAddr, rsp := .ofNat stackAddr,rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102},
    dmem := memory bits},AllowedipsImage.Lookup.entry⟩

def coverage : CommonBitsCoverage.Context := ⟨Witness.coverage.coverage,0⟩

private instance (x : Except String Unit) : Decidable (x = .ok ()) :=
  match x with
  | .error e => .isFalse (by intro h; cases h)
  | .ok () => .isTrue rfl

theorem check4 : callBoundary Witness.names Witness.input coverage (state 32) (Witness.world 32)
    (some 0) 32 1 (.ofNat stopAddr) = .ok () := by
  simp only [callBoundary,assertAt,callInput,callFrameCheck,networkKeyCheck,coverageCheck,coverageDataCheck,
    reconstruct,decodeNode,word,load64,load32,Mem.loadInt,state,memory_load]
  decide +kernel

theorem check6 : callBoundary Witness.names Witness.input coverage (state 128) (Witness.world 128)
    (some 0) 128 1 (.ofNat stopAddr) = .ok () := by
  simp only [callBoundary,assertAt,callInput,callFrameCheck,networkKeyCheck,coverageCheck,coverageDataCheck,
    reconstruct,decodeNode,word,load64,load32,Mem.loadInt,state,memory_load]
  decide +kernel

theorem pre (bits : Nat) (family : bits=32 ∨ bits=128) :
    Pre_allowedips (callConfig Witness.names (Witness.world bits) (Witness.device bits) (some 0) bits 1)
      coverage.coverage 0 (.ofNat stopAddr) (state bits) (Witness.world bits) := by
  have checked : callBoundary Witness.names Witness.input coverage (state bits) (Witness.world bits)
      (some 0) bits 1 (.ofNat stopAddr) = .ok () := by
    rcases family with rfl | rfl
    · exact check4
    · exact check6
  obtain ⟨d,device,pre,_⟩ := callBoundary_pre checked
  have equal : Witness.device bits = d := Option.some.inj device
  subst d
  exact ⟨_,pre⟩

theorem accepted (bits : Nat) (family : bits=32 ∨ bits=128) :
    ∃ final, (Source.lookup (some 0) bits 1).run (Witness.world bits)=.ok (some 0,final) := by
  have result : ((Source.lookup (some 0) bits 1).run (Witness.world bits)).toOption.map Prod.fst=some (some 0) := by
    rcases family with rfl | rfl
    all_goals
      unfold Source.lookup Leanux.WG.lookup Leanux.WG.findNode
      simp only [Std.Legacy.Range.forIn_eq_forIn_range']
      decide +kernel
  cases actual : (Source.lookup (some 0) bits 1).run (Witness.world bits) with
  | error e => rw [actual] at result; cases result
  | ok value =>
    obtain ⟨answer,final⟩ := value
    rw [actual] at result
    have equal : answer=some 0 := Option.some.inj result
    exact ⟨final,by rw [equal]⟩

#print axioms accepted
#print axioms check4
#print axioms check6
#print axioms pre
end Binary.Pair.Trie.CallWitness
