import Main
import AllowedipsSourceWitness
import AllowedipsObservation

/-! Executable test of the exact states used by the physical precondition
witnesses. Invoke from binary/ after allowedips_probe.py has reproduced its
inputs: `capped lake env lean AllowedipsWitnessRun.lean`. All anchored and
callback instructions execute under Kraken; failure throws an IO error. -/
namespace Binary.AllowedipsWitness

def runExact (operation : Nat) (initial : MachineState) (expected : Nat) : IO Unit := do
  let path := s!"../.tmp/binary-allowedips/input-{operation}.json"
  let json ← liftE (Lean.Json.parse (← IO.FS.readFile path))
  let input ← liftE (Lean.fromJson? (α := AllowedipsProbe.Input) json)
  unless input.entry == AllowedipsImage.Lookup.entry.toBitVec.toNat &&
      input.preempt == TrustBase.preemptCountAddress.toNat && input.entryPreempt == 512 do
    throw (IO.userError "witness input/image identity mismatch")
  let execute := runProgram input.instructions input.labels input.hooks input.preempt initial
  let result ← liftE (execute 0 true 10000 512)
  let alternate ← liftE (execute 0xffffffffffffffff true 10000 512)
  unless result.state.pc.toBitVec.toNat == 0x500000 &&
      result.state.data.regs.rax.toNat == (peerAddress expected).toNat &&
      result.state.data.regs.rsp.toNat == 0x400808 do
    throw (IO.userError "exact witness did not return the selected peer")
  unless result.pcs == alternate.pcs && result.state.data.regs == alternate.state.data.regs &&
      result.state.data.dmem == alternate.state.data.dmem do
    throw (IO.userError "undefined-value seed changed exact witness execution")
  for reg in [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15] do
    unless result.state.data.regs.get64 reg == initial.data.regs.get64 reg do
      throw (IO.userError "exact witness callee-save mismatch")
  unless (← liftE (readNat result.state input.preempt 4)) == 512 do
    throw (IO.userError "exact witness preempt count not restored")
  unless (← liftE (readNat result.state ((peerAddress expected).toNat + Layouts.peer_refcount) 4)) == 2 do
    throw (IO.userError "exact witness peer reference count mismatch")
  let observed ← liftE (observeHistory (AllowedipsObservation.edge 0) result.history.toList)
  let root := if operation == 5 then some 7 else some 1
  let bits := if operation == 5 then 32 else 128
  let key := if operation == 5 then key4 else key6
  let ((answer, points), final) ← liftE (((AllowedipsSource.lookup root bits key).run []).run world |>.mapError Leanux.Stop.message)
  unless answer == some expected && (.call "lookup" :: observed.map (·.tag)) == points.map (·.tag) &&
      observed.filterMap (·.step) == final.steps.toList do
    throw (IO.userError "exact witness source/binary decision mismatch")
  IO.println s!"allowedips exact witness op={operation}: PASS; executed={result.pcs.size}; decisions={final.steps.size}; returned=0x500000"

#eval runExact 5 initial4 3
#eval runExact 8 initial6 4
end Binary.AllowedipsWitness
