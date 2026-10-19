import CallbackCheck
import ProbeSupport

namespace Binary.Callback
open TrustBase Lean
local instance : Labels := Image.linkedLabels

def address : KcovKind → Nat
  | .pc => 0xffffffff810f3100
  | .cmp4 => 0xffffffff810f3e80
  | .constCmp4 => 0xffffffff810f3f00
  | .constCmp1 => 0xffffffff810f3ec0
  | .cmp1 => 0xffffffff810f3e40
  | .cmp8 => 0xffffffff810f3ea0

/-- Every transition is the fetched instruction. Stopping checks the ABI
return PC and stack together, and never substitutes a service summary. -/
def execute (seed : UInt64) (s : MachineState) : Except String Run := do
  let ra ← readNat s s.data.regs.rsp.toNat 8
  let mut run : Run := {state := s,history := #[s]}
  for _ in [:128] do
    if run.state.pc == Int64.ofNat ra && run.state.data.regs.rsp == s.data.regs.rsp+8 then
      return run
    let pc := run.state.pc
    let some decoded := ServiceImage.fetch pc | throw s!"callback.fetch: {pc.toBitVec.toNat}"
    run := {run with pcs := run.pcs.push pc.toBitVec.toNat}
    run ← interpret seed run decoded.instruction pc.toBitVec.toNat decoded.size
  throw "callback.instruction-budget"

def fixture (entry preempt mode soft capacity count area : Nat) : MachineState := Id.run do
  let mut m : DataMem := {}
  for (a,n,v) in [(preemptCountAddress.toNat,4,preempt),(currentTaskAddress.toNat,8,0x800000),
      (0x8006e0,4,mode),(0x8006e4,4,capacity),(0x8006e8,8,area),(0x800704,4,soft),
      (stackAddr,8,stopAddr),(softirqPendingAddress.toNat,2,0)] do
    m := put m a n v
  -- Map only the small locations this particular plan could touch, including
  -- wrapped offsets. Huge capacity values do not allocate huge test buffers.
  let slot := (32*count+40)%2^64
  for a in [area,(area+8*((count+1)%2^64))%2^64,
      (area+slot+2^64-32)%2^64,(area+slot+2^64-24)%2^64,
      (area+slot+2^64-16)%2^64,(area+slot+2^64-8)%2^64] do
    m := put m a 8 0
  m := put m area 8 count
  let regs : Reg64s := {
    rsp := .ofNat stackAddr
    rdi := 0xfedcba9876543210, rsi := 0xabcdef0123456789
    rbx := 17, rbp := 34, r12 := 51, r13 := 68, r14 := 85, r15 := 102 }
  return ⟨{dmem := m, regs},.ofNat entry⟩

def checkABI (s : MachineState) (run : Run) : Except String Unit := do
  let ra ← readNat s s.data.regs.rsp.toNat 8
  unless run.state.pc==Int64.ofNat ra && run.state.data.regs.rsp==s.data.regs.rsp+8 do
    throw "callback.return"
  for r in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless run.state.data.regs.get64 r == s.data.regs.get64 r do throw "callback.preserved-register"
  unless run.pcs.all (fun pc => (Image.fetch (.ofNat pc)).isNone) do throw "callback.anchor-reentry"

def checkStores (s : MachineState) (run : Run) (stores : List WordWrite) : Except String Unit := do
  let expected := stores.foldl (fun m w => m.storeInt w.address 8 w.value.toInt) s.data.dmem
  for (a,n) in run.writes do
    for i in [:n] do
      let byte : BitVec 64 := .ofNat 64 (a+i)
      unless stores.any (fun w => (List.range 8).any (fun j => w.address+.ofNat 64 j==byte)) do
        throw "callback.unplanned-write"
      unless run.state.data.dmem.get? byte == expected.get? byte do throw "callback.effect"
  for w in stores do
    for i in [:8] do
      let byte := w.address+.ofNat 64 i
      unless run.state.data.dmem.get? byte == expected.get? byte do throw "callback.missing-store"

def checkKcov (kind : KcovKind) (s : MachineState) (seed : UInt64) : Except String Nat := do
  unless readyCheck kind s do throw "callback.not-ready"
  let some stores := KcovPlan kind s | throw "callback.plan"
  let run ← execute seed s
  checkABI s run
  checkStores s run stores
  return run.pcs.size

def suite : Except String Json := do
  for (pc,_,_) in ServiceImage.listing do
    match ServiceImage.fetch (.ofNat pc), ServiceImage.runtimeFetch (.ofNat pc) with
    | none, none =>
      unless pc==0xffffffff810732ea do throw s!"callback.unexpected-rejected-PC: {pc}"
    | some literal, some parsed =>
      unless literal.size==parsed.size && decide (literal.instruction=parsed.instruction) do
        throw s!"callback.literal-drift: {pc}"
    | _, _ => throw s!"callback.literal-missingness-drift: {pc}"
  let mut cases := 0
  let mut instructions := 0
  for kind in [KcovKind.pc,.cmp4,.constCmp4,.constCmp1] do
    for preempt in [0,1,256,512,65536,16711680,16777216] do
      for mode in [0,2,3] do
        for soft in [0,1] do
          for (capacity,count) in [(0,0),(1,0),(2,0),(5,0),(9,1),(9,2),
              (16,2^64-1),(16,2^59),(2^32-1,2^32-1)] do
            for seed in [(0 : UInt64),0xffffffffffffffff] do
              let s := fixture (address kind) preempt mode soft capacity count 0x900000
              instructions := instructions + (← (checkKcov kind s seed).mapError
                (fun e => s!"{e}; kind={address kind} preempt={preempt} mode={mode} soft={soft} cap={capacity} count={count}"))
              cases := cases+1
  -- Benign overlapping destinations (count wrap) and wrapping addresses.
  for kind in [KcovKind.pc,.cmp4,.constCmp4,.constCmp1] do
    for area in [2^64-8,preemptCountAddress.toNat] do
      let s := fixture (address kind) 0 (if kind==.pc then 2 else 3) 0 16 0 area
      instructions := instructions + (← checkKcov kind s 0)
      cases := cases+1
  let bad := fixture (address .pc) 0 2 0 16 0 (stackAddr-8)
  unless !readyCheck .pc bad do throw "callback.control.return-overlap-accepted"
  let mut bhCases := 0
  for count in [0,1,512,1024,0xfff00000] do
    for arg in [0,1,512,1024,0xffffffff] do
      for seed in [(0 : UInt64),0xffffffffffffffff] do
        let s := fixture 0xffffffff810732c0 count 0 0 0 0 0x900000
        let s := {s with data := {s.data with regs := {s.data.regs with rsi := .ofNat arg}}}
        unless bhReadyCheck s do throw "callback.bh.not-ready"
        let run ← execute seed s
        checkABI s run
        let expected := ((BitVec.ofNat 32 count)-BitVec.ofNat 32 arg).toNat
        unless (← readNat run.state preemptCountAddress.toNat 4)==expected do throw "callback.bh.count"
        for (a,n) in run.writes do
          unless a==preemptCountAddress.toNat && n==4 do throw "callback.bh.frame"
        instructions := instructions+run.pcs.size
        bhCases := bhCases+1
  return Json.mkObj [("status",toJson "pass"),("origin",toJson "generated states"),
    ("kcov_cases",toJson cases),("bh_cases",toJson bhCases),("instructions",toJson instructions),
    ("return_overlap_control",toJson "rejected")]

end Binary.Callback
