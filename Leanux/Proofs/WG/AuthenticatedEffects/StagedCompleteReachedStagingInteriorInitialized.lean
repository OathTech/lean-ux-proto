import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingInteriorObserver
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitInitialized

/-! The initialized routed front supplies the account for its next native
take. The silent clear retains its original cohort, then the actual receipt
moves that cohort to the selected location before the key-borrow child. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open TransmitSecurity CausalJournal CompleteCarrier Staged.Obligations
open HandshakeSecurity.StagedConservation StagingInterior

theorem Caller.take_interval
    (caller : Caller trace placeholders operationIndex world history)
    (front : Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient
      (.ok pid) v b prior)
    (device : v.dev=some d) (resident : d.peers[pid]?=some p)
    (nonempty : p.staged.isEmpty=false) :
    ∃ ledger,
      let events := Transmit.resultHistory caller.input (.ok pid) caller.entered.wg v caller.entered.ambient b prior
      let cleared := queueWorld pid p [] d v
      let clockAfter := clock b .stagedEmpty false
      let receipt : Take.Receipt := ⟨pid,⟨some p,v,cleared,b,clockAfter⟩⟩
      ((Take.takePrefix pid).run v).run b=.ok ((some p,cleared),clockAfter) ∧
      Staged.Origins.Aligned (Staged.Origins.Born events d.ifindex pid p.internalId)
        (pendingAt (.staged d.ifindex pid p.internalId) ledger) p.staged ∧
      Staged.stagedAt cleared pid=some (p.internalId,[]) ∧
      Staged.dropped cleared=Staged.dropped v ∧
      ∃ next generation, Staged.Obligations.Step ledger next ∧
        next=transferLocation (.staged generation pid p.internalId) (.selected events.length) ledger ∧
        CompleteSelected.Ready next [] [] generation pid p events.length
          (events++[.stagingTaken receipt]) cleared clockAfter ∧
        StagedEntry.SelectionContinuation receipt events := by
  obtain ⟨ledger,before⟩ := caller.front_accounted front
  obtain ⟨native,aligned,empty,counter⟩ := take_pending before device resident nonempty (a:=b)
  exact ⟨ledger,native,aligned,empty,counter,take_recorded before device resident nonempty (a:=b)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
