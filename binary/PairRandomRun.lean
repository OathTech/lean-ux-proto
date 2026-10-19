import RandomImage
import ServiceImage
import ProbeSupport
import TrustBase
import RandomState
import RandomReadyCheck

namespace Binary.Pair.RandomRun
open Lean
local instance : Labels := Image.linkedLabels

def privateConfig : RandomProvider.Config := {
  blocks := [(RandomProvider.Layout.readyAddress,4),(RandomProvider.Layout.cacheAddress,108),
    (RandomProvider.Layout.cpuAddress,40),(RandomProvider.Layout.baseAddress,40)] }

/-- Concrete decoded-body execution; no supplied service return. The decoder
is deliberately partial, and any departure reports its exact PC. -/
def fetch (pc : Int64) : Option Decoded :=
  (RandomImage.fetch pc).orElse (fun _ => ServiceImage.fetch pc)

def repeatedString : Instr → Bool
  | .regular .W64 _ (.movs true) | .regular .W64 _ (.stos true) => true
  | _ => false

/-- QEMU reports each REP iteration at the same PC. Kraken's corresponding
instruction executes the whole repeat. Execution below separately checks
the exact stop multiplicity against the actual entry RCX. -/
def instructionPCs (stops : Array Nat) : Array Nat := Id.run do
  let mut pcs := #[]
  for pc in stops do
    if pcs.back?==some pc && ((fetch (.ofNat pc)).any (fun d => repeatedString d.instruction)) then
      continue
    pcs := pcs.push pc
  return pcs

def context (active : Bool) : CommonBitsCoverage.Context :=
  ⟨⟨0x800000,if active then 0x900000 else 0,if active then 512 else 0,
      if active then 2 else 0,0⟩,512⟩

/-- Test the physical postcondition without choosing the returned draw.
Endpoint equality outside the footprint permits balanced transient stores,
such as preempt_count, whose original bytes are restored before return. -/
def physicalPost (config : RandomProvider.Config) (c : CommonBitsCoverage.Context)
    (initial : MachineState) (after : Run) (returnPC : Int64) : Except String Unit := do
  unless after.state.pc==returnPC && after.state.data.regs.rsp==initial.data.regs.rsp+8 do
    throw "random.contract.return"
  for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless after.state.data.regs.get64 reg==initial.data.regs.get64 reg do throw "random.contract.ABI"
  unless Trie.coverageCheck c after.state.data.dmem do throw "random.contract.coverage-preempt"
  RandomProvider.check config c.coverage.task.toNat
    (TrustBase.RandomRecordingActive c.coverage c.preempt) after.state.data.dmem
  unless after.state.data.system.bits[9]==initial.data.system.bits[9] do throw "random.contract.IF"
  unless after.pcs.all (fun pc => (IndexInsertImage.Insert.fetch (.ofNat pc)).isNone) do
    throw "random.contract.anchor-reentry"
  for (address,size) in after.writes do
    for offset in [:size] do
      let a := address+offset
      unless config.blocks.any (fun (base,size) => base≤a && a<base+size) ||
          (initial.data.regs.rsp.toNat-1024≤a && a<initial.data.regs.rsp.toNat) ||
          (decide c.Needed && c.coverage.area.toNat≤a && a<c.coverage.area.toNat+8*c.coverage.capacity.toNat) do
        unless initial.data.dmem.get? (.ofNat 64 a)==after.state.data.dmem.get? (.ofNat 64 a) do
          throw s!"random.contract.frame: {a}"

def execute (seed : UInt64) (budget : Nat) (initial : MachineState) (returnPC : Int64)
    (native : Option (Array Nat) := none) : Except String Run := do
  let mut run : Run := {state := initial}
  let mut stopCursor := 0
  for _ in [:budget] do
    if run.state.pc==returnPC then
      if let some stops := native then
        unless stopCursor==stops.size do throw "random.body.native-unconsumed"
      return run
    let pc := run.state.pc
    let some decoded := fetch pc | throw s!"random.body.missing-PC: {pc.toBitVec.toNat}"
    if let some stops := native then
      let count := if repeatedString decoded.instruction then max 1 run.state.data.regs.rcx.toNat else 1
      unless stopCursor+count≤stops.size &&
          (stops.extract stopCursor (stopCursor+count)).all (· == pc.toBitVec.toNat) do
        throw s!"random.body.native-PC-or-REP-count: {pc.toBitVec.toNat}, cursor={stopCursor}, count={count}"
      stopCursor := stopCursor+count
    run := {run with pcs := run.pcs.push pc.toBitVec.toNat}
    run ← (interpret seed run decoded.instruction pc.toBitVec.toNat decoded.size (some #[])).mapError
      (fun error => s!"random.body at {pc.toBitVec.toNat}: {error}")
  throw "random.body.instruction-budget"

/-- Synthetic private provider state for concrete positive entry evidence.
It exercises the ready, cached path with recording disabled. It is not a
captured snapshot and is not the general provider readiness declaration. -/
def cachedState (interrupts : Bool) : MachineState := Id.run do
  let mut m : DataMem := (List.replicate 4096 (0 : UInt8)).At 0x400000
  for (address,width,value) in
      [(stackAddr,8,stopAddr),(TrustBase.currentTaskAddress.toNat,8,0x800000),
       (TrustBase.preemptCountAddress.toNat,4,512),(0x8006e0,4,0),
       (0xffffffff81fdbaf8,4,1),(0xffffffff81fdbae0,8,1),
       (0xffffffff81cbba60,8,1),(0xffffffff81cbba68,4,0)] do
    m := put m address width value
  for i in [:24] do m := put m (0xffffffff81cbba00+4*i) 4 (7+8192*i)
  for i in [:32] do
    m := put m (0xffffffff81cbbb80+i) 1 i
    m := put m (0xffffffff81fdbac0+i) 1 (31-i)
  m := put m 0xffffffff81cbbba0 8 1
  return ⟨{
    dmem := m
    system := {bits := (if interrupts then 512 else 0),cpl := 0}
    regs := {rsp := .ofNat stackAddr,rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102}},
    .ofNat 0xffffffff81375200⟩

def recordingState (remote : Bool) : MachineState × RandomProvider.Config := Id.run do
  let initial := cachedState true
  let extra := [(0x8006f0,16),(0x800000+RandomProvider.Layout.taskDropped,4),(0xa00000,56),(0xb00000,192),
    (RandomProvider.Layout.sequenceAddress,8)] ++
    (if remote then [(0xc00000,32),(RandomProvider.Layout.remoteMapAddress,128)] else [])
  let mut m := initial.data.dmem
  for (base,size) in (0x900000,4096)::extra do
    for i in [:size] do m := put m (base+i) 1 0
  for (address,width,value) in [(0x8006e0,4,2),(0x8006e4,4,512),(0x8006e8,8,0x900000),
      (0x8006f0,8,if remote then 0 else 0xa00000),(0x8006f8,8,if remote then 0x123 else 0),
      (0xa00030,8,0xb00000),(0xb00000,4,2)] do
    m := put m address width value
  for i in [:2] do
    let e := 0xb00010+i*RandomProvider.Layout.entrySize
    m := put m e 8 stopAddr
    m := put m (e+32) 4 104
    m := put m (e+36) 4 4
    m := put m (e+48) 4 (41+i)
  if remote then
    m := put m 0xc00000 8 0x123
    m := put m 0xc00008 8 0xa00000
    let bucket := (0x123*0x61c8864680b583eb%2^64)/2^60
    m := put m (RandomProvider.Layout.remoteMapAddress+8*bucket) 8 0xc00010
  return ({initial with data := {initial.data with dmem := m}},
    {blocks := privateConfig.blocks++extra,remoteNodes := if remote then [0xc00000] else []})

def suite : Except String Json := do
  let mut results := #[]
  for interrupts in [false,true] do
    for seed in [(0 : UInt64),0xffffffffffffffff] do
      let mut initial := cachedState interrupts
      for ordinal in [:2] do
        RandomProvider.readyCheck privateConfig (context false) initial
        RandomProvider.check privateConfig 0x800000 false initial.data.dmem
        let after ← execute seed 2000 initial (.ofNat stopAddr)
        physicalPost privateConfig (context false) initial after (.ofNat stopAddr)
        RandomProvider.check privateConfig 0x800000 false after.state.data.dmem
        unless after.state.data.regs.rax.toNat==7+8192*ordinal &&
            after.state.data.regs.rsp.toNat==stackAddr+8 do throw "random.body.result-stack"
        for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
          unless after.state.data.regs.get64 reg==initial.data.regs.get64 reg do
            throw "random.body.callee-save"
        unless after.state.data.system.cpl==0 && after.state.data.system.bits[9]==interrupts do
          throw "random.body.privilege-IF"
        unless (← readNat after.state 0xffffffff81cbba68 4)==ordinal+1 &&
            (← readNat after.state (0xffffffff81cbba00+4*ordinal) 4)==0 do
          throw "random.body.cache-effect"
        results := results.push (Json.mkObj [("interrupts_enabled",toJson interrupts),
          ("seed",toJson seed.toNat),("ordinal",toJson ordinal),
          ("instructions",toJson after.pcs.size),("value",toJson after.state.data.regs.rax.toNat)])
        initial := ⟨{after.state.data with regs := {after.state.data.regs with rsp := .ofNat stackAddr}},
          .ofNat 0xffffffff81375200⟩
  let mut refills := #[]
  for generation in [1,2] do
    let start := cachedState true
    let mut memory := start.data.dmem
    for i in [:32] do
      memory := put memory (0xffffffff81cbbb80+i) 1 i
      memory := put memory (0xffffffff81fdbac0+i) 1 (31-i)
    memory := put memory 0xffffffff81cbbba0 8 generation
    memory := put memory 0xffffffff81cbba68 4 24
    let mut initial := {start with data := {start.data with dmem := memory}}
    for ordinal in [:2] do
      RandomProvider.readyCheck privateConfig (context false) initial
      RandomProvider.check privateConfig 0x800000 false initial.data.dmem
      let after ← execute 0 20000 initial (.ofNat stopAddr)
      physicalPost privateConfig (context false) initial after (.ofNat stopAddr)
      RandomProvider.check privateConfig 0x800000 false after.state.data.dmem
      unless after.state.data.regs.rsp.toNat==stackAddr+8 &&
          after.state.data.system.bits[9] && after.state.data.system.cpl==0 do
        throw "random.refill.stack-system"
      for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
        unless after.state.data.regs.get64 reg==initial.data.regs.get64 reg do
          throw "random.refill.callee-save"
      unless (← readNat after.state 0xffffffff81cbba68 4)==ordinal+1 &&
          (← readNat after.state 0xffffffff81cbba60 8)==1 &&
          (← readNat after.state (0xffffffff81cbba00+4*ordinal) 4)==0 do
        throw "random.refill.cache-effect"
      refills := refills.push (Json.mkObj [("starting_crng_generation",toJson generation),
        ("ordinal",toJson ordinal),("instructions",toJson after.pcs.size),
        ("value",toJson after.state.data.regs.rax.toNat)])
      initial := ⟨{after.state.data with regs := {after.state.data.regs with rsp := .ofNat stackAddr}},
        .ofNat 0xffffffff81375200⟩
  let mut steered := #[]
  for remote in [false,true] do
    let (start,config) := recordingState remote
    let mut initial := start
    for ordinal in [:3] do
      RandomProvider.readyCheck config (context true) initial
      RandomProvider.check config 0x800000 true initial.data.dmem
      let after ← execute 0 20000 initial (.ofNat stopAddr)
      physicalPost config (context true) initial after (.ofNat stopAddr)
      RandomProvider.check config 0x800000 true after.state.data.dmem
      let expected := if ordinal<2 then 41+ordinal else 7+8192*ordinal
      unless after.state.data.regs.rax.toNat==expected &&
          (← readNat after.state 0xb00004 4)==min (ordinal+1) 2 &&
          (← readNat after.state 0xb00008 4)==(if ordinal<2 then 0 else 1) do
        throw "random.recording.result-or-cursor"
      unless after.state.data.regs.rsp.toNat==stackAddr+8 &&
          after.state.data.system.bits[9] && after.state.data.system.cpl==0 do
        throw "random.recording.stack-system"
      for reg in [Reg64.rbx,.rbp,.r12,.r13,.r14,.r15] do
        unless after.state.data.regs.get64 reg==initial.data.regs.get64 reg do
          throw "random.recording.callee-save"
      steered := steered.push (Json.mkObj [("remote",toJson remote),("ordinal",toJson ordinal),
        ("instructions",toJson after.pcs.size),("value",toJson expected)])
      initial := ⟨{after.state.data with regs := {after.state.data.regs with rsp := .ofNat stackAddr}},
        .ofNat 0xffffffff81375200⟩
  -- A saturated choice record updates the per-task dropped counter. This
  -- resource was discovered by the retained-heap mixed-call tests.
  let (saturationStart,saturationConfig) := recordingState false
  let saturationState := {saturationStart with data := {saturationStart.data with
    dmem := put saturationStart.data.dmem 0x8006e4 4 4}}
  let saturationContext : CommonBitsCoverage.Context :=
    {(context true) with coverage := {(context true).coverage with capacity := 4}}
  RandomProvider.readyCheck saturationConfig saturationContext saturationState
  let saturation ← execute 0 20000 saturationState (.ofNat stopAddr)
  physicalPost saturationConfig saturationContext saturationState saturation (.ofNat stopAddr)
  unless saturation.state.data.regs.rax==41 &&
      (← readNat saturation.state (0x800000+RandomProvider.Layout.taskDropped) 4)==1 do
    throw "random.saturation.counter"
  let omitted := {saturationConfig with
    blocks := saturationConfig.blocks.filter
      (fun span => span.1 != 0x800000+RandomProvider.Layout.taskDropped)}
  match RandomProvider.readyCheck omitted saturationContext saturationState with
  | .ok _ => throw "random.saturation.control: omitted dropped-counter allocation accepted"
  | .error error => unless error=="random.private.region-unmapped" do
      throw s!"random.saturation.control failed elsewhere: {error}"
  -- Review counterexample: the global sequence increment aliases a steering
  -- head, invalidating head≤count. Cover-block disjointness alone misses it.
  let (aliasStart,aliasConfig) := recordingState false
  let aliasAddress := RandomProvider.Layout.sequenceAddress-4
  let aliasMemory := put
    (put aliasStart.data.dmem (0xa00000+RandomProvider.Layout.objectSteer) 8 aliasAddress)
    aliasAddress 12 0
  let aliasState := {aliasStart with data := {aliasStart.data with dmem := aliasMemory}}
  for separateCover in [false,true] do
    let blocks := if separateCover then
      aliasConfig.blocks.filter (fun span => span.1 != RandomProvider.Layout.sequenceAddress)
      else aliasConfig.blocks
    let config := {aliasConfig with blocks := blocks++[(aliasAddress,12)]}
    match RandomProvider.readyCheck config (context true) aliasState with
    | .ok _ => throw "random.role-control: sequence/steering alias accepted"
    | .error error => unless error=="random.private.role-alias" do
        throw s!"random.role-control failed elsewhere: {error}"
    let after ← execute 0 20000 aliasState (.ofNat stopAddr)
    unless (← readNat after.state aliasAddress 4)==0 &&
        (← readNat after.state (aliasAddress+4) 4)==1 do
      throw "random.role-control.counterexample-not-reproduced"
    match physicalPost config (context true) aliasState after (.ofNat stopAddr) with
    | .ok _ => throw "random.role-control: invalid post accepted"
    | .error error => unless error=="random.private.steering-counts" do
        throw s!"random.role-control post failed elsewhere: {error}"
  -- Consistent overlapping capture covers remain valid when roles are apart.
  RandomProvider.readyCheck {aliasConfig with blocks := aliasConfig.blocks++[(0xb00000,192)]}
    (context true) aliasStart
  -- Changing context/return site can change a draw without changing private
  -- bytes. The coupling specification must therefore fix both parameters.
  let (steerInitial,steerConfig) := recordingState false
  let direct ← execute 0 20000 steerInitial (.ofNat stopAddr)
  let inactive := {steerInitial with data := {steerInitial.data with
    dmem := put steerInitial.data.dmem 0x8006e0 4 0}}
  let otherSite := {steerInitial with data := {steerInitial.data with
    dmem := put steerInitial.data.dmem stackAddr 8 (stopAddr+8)}}
  for candidate in [inactive,otherSite] do
    unless RandomProvider.snapshot steerConfig.blocks candidate.data.dmem==
        RandomProvider.snapshot steerConfig.blocks steerInitial.data.dmem do
      throw "random.coupling-control.private-bytes-changed"
  RandomProvider.readyCheck steerConfig (context false) inactive
  RandomProvider.readyCheck steerConfig (context true) otherSite
  let raw ← execute 0 20000 inactive (.ofNat stopAddr)
  let misplaced ← execute 0 20000 otherSite (.ofNat (stopAddr+8))
  unless direct.state.data.regs.rax==41 && raw.state.data.regs.rax==7 &&
      misplaced.state.data.regs.rax==7 do throw "random.coupling-control.expected-distinction"
  -- Dropping REP iteration stops must fail at the native-trace check.
  match execute 0 20000 steerInitial (.ofNat stopAddr) (some direct.pcs) with
  | .ok _ => throw "random.REP-control: collapsed native stops accepted"
  | .error error => unless error.startsWith "random.body.native-PC-or-REP-count:" do
      throw s!"random.REP-control failed elsewhere: {error}"
  let initial := cachedState true
  let after ← execute 0 2000 initial (.ofNat stopAddr)
  let outside := stackAddr+8
  let corrupt := {after with
    state := {after.state with data := {after.state.data with
      dmem := after.state.data.dmem.insert (.ofNat 64 outside) 1}},
    writes := after.writes.push (outside,1)}
  for (expected,result) in [
      ("random.ready.stack",RandomProvider.readyCheck privateConfig (context false)
        {initial with data := {initial.data with dmem := initial.data.dmem.erase (.ofNat 64 (stackAddr-1000))}}),
      ("random.ready.private-alias",RandomProvider.readyCheck
        {privateConfig with blocks := privateConfig.blocks++[(stackAddr-8,8)]} (context false) initial),
      ("random.ready.direction",RandomProvider.readyCheck privateConfig (context false)
        {initial with data := {initial.data with system := {bits := 1536,cpl := 0}}}),
      (s!"random.contract.frame: {outside}",physicalPost privateConfig (context false) initial corrupt (.ofNat stopAddr))] do
    match result with
    | .ok _ => throw s!"random.control accepted: {expected}"
    | .error error => unless error==expected do throw s!"random.control failed elsewhere: {expected}: {error}"
  let missingCache := initial.data.dmem.erase (.ofNat 64 RandomProvider.Layout.cacheAddress)
  match RandomProvider.check privateConfig 0x800000 false missingCache with
  | .ok _ => throw "random.private.control: missing cache byte accepted"
  | .error error => unless error=="random.private.allocation-unmapped" do
      throw s!"random.private.control failed elsewhere: {error}"
  let bad := {initial with data := {initial.data with system := {initial.data.system with cpl := 3}}}
  let rejection ← match execute 0 2000 bad (.ofNat stopAddr) with
    | .ok _ => throw "random.body.control: unprivileged CLI accepted"
    | .error error => do
      unless error.endsWith "CLI: #GP(0), CPL exceeds IOPL in 64-bit mode" do
        throw s!"random.body.control failed elsewhere: {error}"
      pure error
  return Json.mkObj [("status",toJson "pass"),
    ("scope",toJson "actual cached/refill random body and recording callbacks, synthetic memory"),
    ("runs",toJson results),("refills",toJson refills),("privilege_control",toJson rejection),
    ("saturation",toJson "actual body increments dropped counter; omitted allocation rejected"),
    ("internal_alias_control",toJson "sequence/steering alias rejected with overlapping and disjoint covers; actual bad post reproduced"),
    ("steered",toJson steered),("private_state_control",toJson "missing cache byte rejected"),
    ("resource_controls",toJson ["missing stack byte","private alias","DF set","write outside footprint"]),
    ("coupling_controls",toJson ["identical private bytes: steered 41, recording disabled 7, other return site 7",
      "missing REP iteration stops rejected"])]

end Binary.Pair.RandomRun
