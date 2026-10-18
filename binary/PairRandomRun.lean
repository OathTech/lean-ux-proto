import RandomImage
import ServiceImage
import ProbeSupport
import TrustBase

namespace Binary.Pair.RandomRun
open Lean
local instance : Labels := Image.linkedLabels

/-- Concrete decoded-body execution; no supplied service return. The decoder
is deliberately partial, and any departure reports its exact PC. -/
def fetch (pc : Int64) : Option Decoded :=
  (RandomImage.fetch pc).orElse (fun _ => ServiceImage.fetch pc)

def execute (seed : UInt64) (budget : Nat) (initial : MachineState) (returnPC : Int64) : Except String Run := do
  let mut run : Run := {state := initial}
  for _ in [:budget] do
    if run.state.pc==returnPC then return run
    let pc := run.state.pc
    let some decoded := fetch pc | throw s!"random.body.missing-PC: {pc.toBitVec.toNat}"
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
  return ⟨{
    dmem := m
    system := {bits := (if interrupts then 512 else 0),cpl := 0}
    regs := {rsp := .ofNat stackAddr,rbx := 17,rbp := 34,r12 := 51,r13 := 68,r14 := 85,r15 := 102}},
    .ofNat 0xffffffff81375000⟩

def suite : Except String Json := do
  let mut results := #[]
  for interrupts in [false,true] do
    for seed in [(0 : UInt64),0xffffffffffffffff] do
      let mut initial := cachedState interrupts
      for ordinal in [:2] do
        let after ← execute seed 2000 initial (.ofNat stopAddr)
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
          .ofNat 0xffffffff81375000⟩
  let initial := cachedState true
  let bad := {initial with data := {initial.data with system := {initial.data.system with cpl := 3}}}
  let rejection ← match execute 0 2000 bad (.ofNat stopAddr) with
    | .ok _ => throw "random.body.control: unprivileged CLI accepted"
    | .error error => do
      unless error.endsWith "CLI: #GP(0), CPL exceeds IOPL in 64-bit mode" do
        throw s!"random.body.control failed elsewhere: {error}"
      pure error
  return Json.mkObj [("status",toJson "pass"),
    ("scope",toJson "actual cached random body and callbacks, synthetic memory, recording disabled; refill not covered"),
    ("runs",toJson results),("privilege_control",toJson rejection)]

end Binary.Pair.RandomRun
