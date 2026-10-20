import KcovInvariant
import ServiceComposition

namespace Binary.Kcov
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Apply a named callback contract from physical entry data. Its poststate
    carries the invariant needed for later calls, along with the actual run.
    No contract says that the mirror relation is preserved. -/
theorem callback (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : ServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (layout : KcovLayout) (preempt : BitVec 32) (s : MachineState) (returnAddress : UInt64)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : KcovState layout preempt s.data.dmem)
    (stack : KcovSeparated layout (InRange s.data.regs.rsp.toBitVec 8))
    (metadata : KcovSeparated layout (KcovMetadataBytes layout))
    (preemptFrame : KcovSeparated layout (InRange preemptCountAddress 4)) :
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        KcovState layout preempt t.machine.data.dmem ∧
        EqualOutside (KcovBufferBytes layout) s.data.dmem t.machine.data.dmem ∧
        NoAnchoredReentry t.history) ⟨s, [s]⟩ := by
  have returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnAddress.toBitVec := by
    simp only [load64, entry.2, Option.map_some, BitVec.ofInt_natCast]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    simp
  have run := contract s returnAddress atEntry
    (state_ready kind layout s preempt returnAddress.toBitVec state returnRead stack) entry
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨returned, frame, effect, noReentry⟩
  have preserved := state_preserved kind layout s t.machine preempt returnAddress.toBitVec
    state returnRead metadata preemptFrame effect frame
  exact ⟨returned, preserved.1, preserved.2, noReentry⟩

/-- The endpoint view used while composing a helper's physical regions.
    Per-cut correspondence is proved on the full history separately. -/
theorem callback_endpoint (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : ServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (layout : KcovLayout) (preempt : BitVec 32) (s : MachineState) (returnAddress : UInt64)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : KcovState layout preempt s.data.dmem)
    (stack : KcovSeparated layout (InRange s.data.regs.rsp.toBitVec 8))
    (metadata : KcovSeparated layout (KcovMetadataBytes layout))
    (preemptFrame : KcovSeparated layout (InRange preemptCountAddress 4)) :
    Eventually (instructionStep fetch)
      (fun t => Returned s t returnAddress ∧ KcovState layout preempt t.data.dmem ∧
        EqualOutside (KcovBufferBytes layout) s.data.dmem t.data.dmem) s := by
  have run := callback fetch address kind contract layout preempt s returnAddress
    atEntry entry state stack metadata preemptFrame
  have projected := history_project fetch _ _ run
  apply eventually_weaken (instructionStep fetch) _ _ _ _ projected
  rintro t ⟨_, returned, state, frame, _⟩
  exact ⟨returned, state, frame⟩

#print axioms callback
#print axioms callback_endpoint
end Binary.Kcov
