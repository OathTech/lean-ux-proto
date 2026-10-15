import Main
import LookupWitnessState

/-! Executable witness check; this module is not imported by a proof.
    First require binary/run.py to succeed on the recorded same-bucket miss;
    merely regenerating input.json does not establish the kernel comparison. Failure is an IO error, never an ignored Bool. -/
namespace LookupWitnessTest
open Binary Leanux Lean

def check : IO Unit := do
  let input : ProbeInput ← liftE (Json.parse (← IO.FS.readFile "../.tmp/binary-tv/input.json") >>= fromJson?)
  unless input.query == LookupWitness.config.query && input.operation == 3 do
    throw (IO.userError "witness requires recorded same-bucket miss operation 3")
  let recorded ← liftE (replayPrefix input.trace input.operation)
  let some actual := LookupRelation.project LookupWitness.config recorded
    | throw (IO.userError "recorded prefix has no lookup projection")
  unless actual.bucket == LookupWitness.view.bucket &&
      actual.ownerWord == LookupWitness.view.ownerWord && actual.count == LookupWitness.view.count &&
      recorded.steps.isEmpty && recorded.netRxSection == LookupWitness.config.rxSection do
    throw (IO.userError "witness projection differs from the recorded entry")
  let expected ← liftE (probe input true)
  let first ← liftE (runMachine input LookupWitness.initial 0 true)
  let second ← liftE (runMachine input LookupWitness.initial 0xffffffffffffffff true)
  unless first.state.pc == Int64.ofNat stopAddr && first.state.data.regs.rax == 0 &&
      first.state.data.regs.rsp == LookupWitness.data.regs.rsp+8 do
    throw (IO.userError "witness did not return NULL into the entry frame")
  unless first.state.data.regs == second.state.data.regs && first.state.data.dmem == second.state.data.dmem &&
      first.coverage == second.coverage && first.comparisons == second.comparisons && first.pcs == second.pcs do
    throw (IO.userError "witness depends on undefined-value seed")
  for reg in [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] do
    unless first.state.data.regs.get64 reg == LookupWitness.data.regs.get64 reg do
      throw (IO.userError "witness changed a callee-save register")
  let expectedCoverage : Array Nat ← liftE (expected.getObjValAs? (Array Nat) "coverage")
  let expectedComparisons : Array (Nat × Nat × Nat) ← liftE
    (expected.getObjValAs? (Array (Nat × Nat × Nat)) "comparisons")
  unless first.coverage == expectedCoverage && first.comparisons == expectedComparisons do
    throw (IO.userError "witness coverage/operands differ from the reference Lean probe")
  let points ← liftE (LookupObservation.observe LookupWitness.config.rxSection first.history.toList)
  let (answer, final) ← liftE ((WG.indexLookup [.handshake] LookupWitness.config.query).run
    LookupWitness.world |>.mapError Stop.message)
  unless answer.isNone && points.filterMap (·.step) == final.steps.toList do
    throw (IO.userError "witness decisions differ from its accepted mirror run")
  IO.println s!"PASS: exact Lean witness, {first.pcs.size} instructions, {points.length} points, two undefined-value seeds; recorded read projection, reference-probe coverage/operands and mirror decisions agree"

#eval check
end LookupWitnessTest
