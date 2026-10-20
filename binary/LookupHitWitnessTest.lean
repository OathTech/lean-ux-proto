import SourceAdapter
import Main
import LookupHitWitnessState

/-! Concrete execution test, outside the proof import closure. First run
    binary/run.py on d1_second_response; the zero-count mutation tests the
    admitted dead-peer domain, not reachability from the recorded prefix. -/
namespace LookupHitWitnessTest
open Binary Leanux Lean

def check : IO Unit := do
  let input : ProbeInput ← liftE (Json.parse (← IO.FS.readFile "../.tmp/binary-tv/input.json") >>= fromJson?)
  unless input.query == LookupHitWitness.config.query && input.operation == 3 do
    throw (IO.userError "hit witnesses require recorded live-hit operation 3")
  let recorded ← liftE (replayPrefix input.trace input.operation)
  let some actual := LookupRelation.project LookupHitWitness.config recorded
    | throw (IO.userError "recorded prefix has no lookup projection")
  let liveView := LookupHitWitness.view true
  unless actual.bucket == liveView.bucket && actual.ownerWord == liveView.ownerWord &&
      actual.count == liveView.count && recorded.steps.isEmpty &&
      recorded.netRxSection == LookupHitWitness.config.rxSection do
    throw (IO.userError s!"live witness projection differs from the recorded entry: count={actual.count}")
  let expected ← liftE (probe input true)
  for live in [false, true] do
    let initial := LookupHitWitness.initial live
    let first ← liftE (runMachine input initial 0 true)
    let second ← liftE (runMachine input initial 0xffffffffffffffff true)
    unless first.state.pc == Int64.ofNat stopAddr &&
        first.state.data.regs.rax == (if live then 0x6000e0 else 0) &&
        first.state.data.regs.rsp == initial.data.regs.rsp+8 do
      throw (IO.userError s!"hit witness live={live} did not return into the entry frame")
    unless first.state.data.regs == second.state.data.regs && first.state.data.dmem == second.state.data.dmem &&
        first.coverage == second.coverage && first.comparisons == second.comparisons && first.pcs == second.pcs do
      throw (IO.userError "hit witness depends on undefined-value seed")
    for reg in [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] do
      unless first.state.data.regs.get64 reg == initial.data.regs.get64 reg do
        throw (IO.userError "hit witness changed a callee-save register")
    unless first.state.data.dmem.loadInt 0x6000e0 8 == some (if live then 0x600000 else 0) &&
        first.state.data.dmem.loadInt 0x600420 4 == some (if live then 2 else 0) &&
        first.state.data.dmem.loadInt 0x300000 8 == some (if live then 0x600000 else 0) do
      throw (IO.userError "hit witness owner/count/output disagrees")
    unless first.state.data.dmem.loadInt TrustBase.preemptCountAddress 4 == some 0 &&
        first.state.data.dmem.loadInt TrustBase.softirqPendingAddress 2 == some 0 do
      throw (IO.userError "hit witness did not restore preempt/pending state")
    let some coverageCount := first.state.data.dmem.loadInt 0x900000 8
      | throw (IO.userError "hit witness lost KCOV header")
    unless 0 ≤ coverageCount && coverageCount ≤ 1024 do
      throw (IO.userError "hit witness broke KCOV header bound")
    if live then
      let expectedCoverage : Array Nat ← liftE (expected.getObjValAs? (Array Nat) "coverage")
      let expectedComparisons : Array (Nat × Nat × Nat) ← liftE
        (expected.getObjValAs? (Array (Nat × Nat × Nat)) "comparisons")
      unless first.coverage == expectedCoverage && first.comparisons == expectedComparisons do
        throw (IO.userError "live witness coverage/operands differ from the recorded reference probe")
    let points ← liftE (LookupObservation.observe LookupHitWitness.config.rxSection first.history.toList)
    let (answer, final) ← liftE ((Source.indexLookup LookupHitWitness.config.kinds LookupHitWitness.config.query).run
      (LookupHitWitness.world live) |>.mapError Stop.message)
    unless answer.isSome == live && points.filterMap (·.step) == final.steps.toList do
      throw (IO.userError "hit witness decisions differ from its accepted mirror run")
    IO.println s!"PASS: exact Lean hit witness live={live}, {first.pcs.size} instructions, {points.length} points, two undefined-value seeds; ABI, owner/count/output and mirror decisions agree"

#eval check
end LookupHitWitnessTest
