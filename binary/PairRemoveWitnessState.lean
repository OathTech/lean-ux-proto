import PairRemove
import LookupWitnessState

namespace Binary.Pair.Remove.Witness
open Leanux Leanux.WG TrustBase

/-- Synthetic positive states: one allocated keypair owner, either linked
as a sole entry or already unhashed. Its peer word is NULL in both cases. -/
def device (linked : Bool) : Device := {
  ifindex := 3,ifname := "wg0",keypairs := ({} : Std.TreeMap Nat Keypair).insert 0 {peer := none},
  indexTable := if linked then [⟨0,.keypair 0⟩] else [] }
def world (linked : Bool) : World :=
  {LookupWitness.world with k := {LookupWitness.world.k with wg := some (device linked)}}
def names : Names := ⟨0x100000,[],[(.keypair 0,0x700000)]⟩
def offsets : Offsets := ⟨65536,0,8,0,32,0,8,0,8,24,28,224,0,0,1056⟩
def context : CommonBitsCoverage.Context := ⟨⟨0x800000,0x900000,4,2,0⟩,0⟩

def words (linked : Bool) : List (Nat×Nat×Nat) :=
  [(0x100000,8,if linked then 0x700008 else 0),
   (0x700000,8,0),(0x700008,8,0),(0x700010,8,if linked then 0x100000 else 0),
   (0x700018,4,2),(0x70001c,4,0),
   (currentTaskAddress.toNat,8,0x800000),(preemptCountAddress.toNat,4,0),
   (softirqPendingAddress.toNat,2,0),(0x8006e0,4,2),(0x8006e4,4,4),
   (0x8006e8,8,0x900000),(0x800704,4,0),
   (0x900000,8,0),(0x900008,8,0),(0x900010,8,0),(0x900018,8,0),
   (stackAddr,8,stopAddr)] ++ (List.range 4).map (fun i => (stackAddr-(i+1)*8,8,0))
def cells (linked : Bool) : List (BitVec 64 × UInt8) :=
  (words linked).flatMap fun (a,size,value) => (Int.toBytes size value).mapIdx (fun i b => (.ofNat 64 (a+i),b))
def memory (linked : Bool) : DataMem :=
  (cells linked).foldr (fun (a,b) m => m.insert a b) ((List.replicate 65536 (0 : UInt8)).At 0x100000)
def frameState (m : DataMem) : MachineState :=
  ⟨{dmem := m,regs := {rdi := 0x100000,rsi := 0x700000,rsp := .ofNat stackAddr,rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102}},.ofNat entry⟩

def state (linked : Bool) : MachineState := frameState (memory linked)

end Binary.Pair.Remove.Witness
