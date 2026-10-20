import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeInterpretation

/-! Fixed staging receipts recover the current-state semantic account on
the very same native world. The source equation and its original receipt
origin are retained beside the derived successor ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting.Receipt
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations RetirementSecurity AllocatedObligation CompleteCarrier
open HandshakeSecurity.StagedConservation

theorem taking (cut : StagingPhase.PendingTake h ledger debts locals pid w a peer v b) :
    let event:=Event.stagingTaken ⟨pid,⟨some peer,w,v,a,b⟩⟩
    (∃after,Current (h++[event]) after debts locals v) ∧
      runWGPrefix (receiptWGObserved (liftWGPrefix (Take.takePrefix pid))
        (fun r=>Event.stagingTaken ⟨pid,r⟩)) w a h=
        runWGPrefix (do emitStatePrefix event; pure (some peer)) v b h := by
  obtain ⟨after,_,_,_,ready⟩:=cut.recorded
  exact ⟨⟨after,Current.of_selected ready⟩,StagingPhase.take_receipt_run cut.native⟩

theorem restoring (cut : StagingPhase.PendingRestore h ledger debts locals generation pid peer position w a v) :
    let event:=Event.stagedRestored ⟨pid,peer.staged,⟨(),w,v,a,a⟩⟩
    (∃after,Current (h++[event]) after debts locals v) ∧
      runWGPrefix (CausalJournal.stagedRestore pid peer.staged) w a h=
        runWGPrefix (do emitStatePrefix event; pure ()) v a h := by
  obtain ⟨d,current,device,resident,_,account⟩:=StagingInterior.restore_ready_total cut.entry
  have same:=Except.ok.inj ((StagingInterior.restore_native (packets:=peer.staged) (a:=a) device resident).symm.trans cut.native)
  have worldEq : StagingInterior.queueWorld pid current (peer.staged++current.staged) d w=v :=
    congrArg (fun out=>out.1.2) same
  refine ⟨?_,Restore.observed_completed Event.stagedRestored pid peer.staged w v a a h cut.native⟩
  rw [←worldEq]
  exact ⟨_,Current.of_accounted account⟩

theorem keepalive (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some peer) (empty : peer.staged.isEmpty=true)
    (allocated : StagingInterior.keepaliveAllocation.run
      (StagingInterior.clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
    let v:=StagingInterior.queueWorld pid peer (peer.staged++[{mtu:=d.mtu}]) d w
    let event:=StagingInterior.keepaliveEvent pid true w v a b
    (∃after,Current (h++[event]) after debts locals v) ∧
      runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=
        runWGPrefix (do emitStatePrefix event; pure true) v b h := by
  have native:=StagingInterior.keepalive_inserted device resident empty allocated
  have recorded:=StagingInterior.keepalive_recorded (h:=h) native
  obtain ⟨_,_,after,account,_⟩:=CompleteKeepalive.normal pid before a b _ _ true recorded
  exact ⟨⟨after,Current.of_accounted account⟩,recorded⟩

theorem routed (before : Accounted h ledger debts locals w)
    (path : Transmit.Path input h w a value v b middle) :
    let event:=StagedAdmission.Front.routedEvent input (Transmit.receipt value w v a b)
    (∃after,Current (middle++[event]) after debts locals v) ∧
      runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h=
        runWGPrefix (do emitStatePrefix event; pure value) v b middle := by
  obtain ⟨after,account,_⟩:=path.accounted before
  exact ⟨⟨after,Current.of_accounted account⟩,path.recorded⟩

theorem trimmed (before : Accounted h ledger debts locals w)
    (performed : ((xmitTrim pid).run w).run a=.ok (((),v),b)) :
    let event:=Event.stagedDisposal (.overflow pid ⟨(),w,v,a,b⟩)
    (∃after,Current (h++[event]) after debts locals v) ∧
      runWGPrefix (StagedAdmission.Front.ops.trim pid) w a h=
        runWGPrefix (do emitStatePrefix event; pure ()) v b h := by
  obtain ⟨after,account,_,recorded⟩:=Transmit.Front.Residual.trim_account before performed
  exact ⟨⟨after,Current.of_accounted account⟩,recorded⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting.Receipt
