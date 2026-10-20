import ProbeSupport

open Lean Leanux Leanux.WG

structure SeqInput where
  seqOffset : Nat
  peerListOffset : Nat
  instructions : Array Instruction
  labels : Array (String × Nat)
  hooks : Array (Nat × String)
  entries : Array Nat
  preempt : Nat
  deriving FromJson

def peer : Peer := {
  remoteStatic := List.replicate 32 0, presharedKey := List.replicate 32 0,
  precomputedStaticStatic := List.replicate 32 0, internalId := 0 }

def world (seq : UInt64) : World := {
  ambient := {env := Leanux.Runner.harnessEnv, timing := Leanux.Env.timing},
  tasks := Leanux.Runner.initialTasks 1024 false false false, fs := {},
  wg := { dev := some {ifindex := 1, ifname := "wg0", peerAllowedips := {seq}, peers := ({} : Std.TreeMap PeerId Peer).insert 0 peer} } }

def witness (input : SeqInput) (family seq : Nat) (seed : UInt64) : Except String Json := do
  let width := if family == 4 then 32 else 128
  let some entry := input.entries[if family == 4 then 0 else 1]? | throw "missing family entry"
  unless seq < 2^64 do throw "sequence witness outside u64"
  let initialWorld := world seq.toUInt64
  let (answer, final) ← (liftWG (insert family 0 (width+1) 0)).run initialWorld |>.mapError Stop.message
  let some d := final.wg.dev | throw "source lost device"
  let mut m : DataMem := (List.replicate 0x810 (0 : UInt8)).At (.ofNat 64 (stackAddr-0x800))
  m := put m stackAddr 8 stopAddr
  m := m.storeBytes 0x100000 (List.replicate 24 0)
  m := put m (0x100000+input.seqOffset) 8 seq
  m := m.storeBytes 0xb00000 (List.replicate 16 0)
  m := m.storeBytes 0x600000 (List.replicate Binary.Layouts.peerSize 0)
  m := put m (0x600000+Binary.Layouts.peer_refcount) 4 peer.refcount
  m := put m (0x600000+input.peerListOffset) 8 (0x600000+input.peerListOffset)
  m := put m (0x600000+input.peerListOffset+8) 8 (0x600000+input.peerListOffset)
  m := materializeServices (put m input.preempt 4 0)
  let regs : Reg64s := {
    rdi := 0x100000,rsi := 0xb00000,rdx := .ofNat (width+1),
    rcx := 0x600000,rsp := .ofNat stackAddr,rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102}
  let initial : MachineState := ⟨{regs,dmem := m},.ofNat entry⟩
  let result ← runUntil input.instructions input.labels input.hooks input.preempt initial seed true 10000 0 #[]
  unless result.state.pc.toBitVec.toNat == stopAddr && result.state.data.regs.rsp.toNat == stackAddr+8 do
    throw "did not reach outer ABI return"
  for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless result.state.data.regs.get64 reg == regs.get64 reg do throw "callee save differs"
  unless answer == -22 && result.state.data.regs.rax.toNat % 2^32 == 2^32-22 do throw "expected EINVAL"
  let actual ← readNat result.state (0x100000+input.seqOffset) 8
  unless actual == (seq+1)%2^64 do throw "unexpected counter values"
  return Json.mkObj [("family",toJson family),("seed",toJson seed.toNat),
    ("entry_seq",toJson seq),("binary_seq",toJson actual),("mirror_seq",toJson d.peerAllowedips.seq.toNat),
    ("equal",toJson (actual == d.peerAllowedips.seq.toNat)),("instructions",toJson result.pcs.size),
    ("result",toJson answer)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: SeqWrap INPUT.json"; return 1
  let input ← liftE (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := SeqInput))
  let mut equal := true
  for family in [4,6] do
    for seq in [1,2^64-1] do
      for seed in [(0 : UInt64),0xffffffffffffffff] do
        let report ← liftE (witness input family seq seed)
        IO.println report.compress
        equal := equal && (← liftE (report.getObjValAs? Bool "equal"))
  if !equal then IO.eprintln "FAIL: allowed-IPs sequence counter differs from the compiled image"
  return if equal then 0 else 1
