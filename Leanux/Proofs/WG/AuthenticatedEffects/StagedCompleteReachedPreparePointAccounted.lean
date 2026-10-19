import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointResidual
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointExecution
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointSourceFrames

/-! The local source points preserve the same ledger at the mapped final
journal history. The incoming canonical Framed certificate is still explicit:
this module does not claim that the full prepare caller derives it, nor that
Iteration.prepare is closed. The setter/cache lemmas supply that next proof. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations StagedTerminalComplete

abbrev OriginEvent := MaterialOrigin.Event RxOrigin.Receipt

def encode (event : OriginEvent) : CausalJournal.Event := .old (.rxOrigin event)

def project (history : List CausalJournal.Event) : List OriginEvent :=
  (history.filterMap CausalJournal.old?).filterMap Journal.origin?

theorem encode_quiet (event : OriginEvent) : birthPackets (encode event)=[] ∧ Quiet (encode event) :=
  ⟨rfl,fun _=>rfl⟩

/-- An actual native cut, including a silent write before its access receipt,
retains the incoming fixed ledger and ownership projection. The source frame
prerequisite is local and remains visible until its whole caller proof. -/
theorem point_accounted
    (before : CompleteCarrier.Accounted history ledger debts locals w)
    (framed : Framed canonical w a (project history))
    (point : Point canonical w a (project history) site v b middle remaining) :
    ∃suffix,middle=project history++suffix ∧
      CompleteCarrier.Accounted (history++suffix.map encode) ledger debts locals v ∧
      runWGPrefix RxOrigin.prepare w a (project history)=runWGPrefix remaining v b middle := by
  obtain ⟨suffix,extended⟩:=point.appends
  refine ⟨suffix,extended,?_,point.run⟩
  apply (before.same_view (point.view framed)).append_quiet
  · intro event member
    obtain ⟨origin,_,rfl⟩:=List.mem_map.mp member
    exact (encode_quiet origin).1
  · intro event member
    obtain ⟨origin,_,rfl⟩:=List.mem_map.mp member
    exact (encode_quiet origin).2

/-- The original action has a complete normal/Stop decomposition through the
fixed source witness. This is source coverage, independently of accounting. -/
theorem original_execution (performed : runWGPrefix RxOrigin.prepare w a h=(result,last)) :
    Execution canonical w a h result last := execution_cases canonical performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
