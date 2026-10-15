import LookupWriteFrame

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation

/-- Concrete lookup result: returned entry pointer and the live peer
    out-parameter. A NULL return makes no claim about untouched output. -/
def LookupResult (c : Config) (entry final : MachineState) (answer : Option (IndexOwner × PeerId)) : Prop :=
  match answer with
  | none => final.data.regs.rax = 0
  | some (owner, peer) => final.data.regs.rax.toBitVec = ownerAddress c owner ∧
      final.data.dmem.loadInt entry.data.regs.rcx.toBitVec 8 = some ((c.peers peer).toNat : Int)

/-- Function postcondition: actual ABI return, exact result and write
    footprint, the actual accepted source run, R at each emitting point and
    each anchored cut, and R at the final state. Source points are the
    executed mirror's Worlds; machine points are observed from raw history. -/
def LookupPost (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (entry : MachineState) (world : World) (answer : Option (IndexOwner × PeerId))
    (finalWorld : World) (final : Executed) : Prop :=
  Returned entry final.machine ra ∧ LookupResult c entry final.machine answer ∧
  ∃ v points source,
    LookupEntry c coverage preempt ra entry world v ∧
    EqualOutside (LookupWrites c coverage preempt entry.data v) entry.data.dmem final.machine.data.dmem ∧
    ((MirrorHistory.lookup c.kinds c.query).run []).run world = .ok ((answer, source), finalWorld) ∧
    observe c.rxSection final.history = .ok points ∧
    MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) points source ∧
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history source ∧
    R c final.history points final.machine finalWorld ∧
    CutFrames (LookupWrites c coverage preempt entry.data v) entry.data.dmem final.history ∧
    EndsAtReturn (Image.Lookup.entry+0x94) final.history

end Binary.LookupRelation
