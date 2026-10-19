import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietNative

/-! Native erasure for enriched non-emitting completion leaves. Independent
history frames are supplied by CallbackQuiet, never inferred from erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackFrames
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues
open HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
variable {F : Type}

theorem product_erases (ρ : E → Option F) {g : PrefixM E α} {t : PrefixM F α}
    {native : Leanux.M α} (projected : ProjectsPrefix ρ id g t) (erased : ErasesPrefix t native) :
    ErasesPrefix g native := by
  intro w h
  have first := congrArg Prod.fst (projected w h)
  have ident : (fun x : α × World => (id x.1,x.2)) = id := by funext x; cases x; rfl
  simp only [ident,Except.map_id] at first
  exact first.symm.trans (erased w (h.filterMap ρ))

theorem lifetime_put_erases (peer : Option PeerId) :
    ErasesStatePrefix (completionLifetime.put peer) (peerPut peer) :=
  RetirementSecurity.NestedPeerRelease.projects_erases old? (completionLifetime_projects.put peer)
    (focusStatePrefix_erases _ _ (peerPutMixed_erases peer))

theorem lifetime_put_quiet (ρ : Event → Option F)
    (old : ∀ event, ρ (LifetimeSource.peerEncode (Event.old ∘ Journal.completionEvent) event) = none)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none) (peer : Option PeerId) :
    CallbackQuiet.StateQuiet ρ (completionLifetime.put peer) :=
  CallbackQuiet.peer ρ _ _ old disposal peer

theorem dispose_erases (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ErasesPrefix (completionOps.dispose pid item key) (liftWG (TxDisposition.disposeSource pid item key)) :=
  product_erases old? (completionOps_projects.dispose pid item key)
    (focusPrefix_erases _ _ (focusPrefix_erases _ _ (TxDisposition.dispose_erases pid item key)))

theorem dead_erases (pid : PeerId) (item : List SkbId) (head : DataPacket) :
    ErasesPrefix (Terminal.deadObserved txEvent txEvent? Event.stagedDisposal Event.terminalDrop pid item head)
      (liftWG (TxDisposition.disposeSource pid item head.keypair)) :=
  product_erases old?
    (Terminal.deadObserved_projects old? txEvent txEvent? Journal.Event.disposition Journal.disposition?
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) Event.stagedDisposal (fun _ => rfl)
      Event.terminalDrop (fun _ => rfl) pid item head)
    (focusPrefix_erases _ _ (TxDisposition.dispose_erases pid item head.keypair))


private theorem nested_quiet_history (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none) (before : List F) :
    RetirementSecurity.NestedPeerRelease.Ops.History (fun h => h.filterMap ρ = before) nested where
  step := Driver.History.state_lift
  release := fun _ => CallbackQuiet.state_history
    (CallbackQuiet.state_focus ρ Event.stagedDisposal stagedDisposal? disposal _) before

theorem rx_finish_quiet (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none) (pid : PeerId) (ready : Packets.RxReady) :
    CallbackQuiet.StateQuiet ρ (RetirementSecurity.NestedPeerRelease.rxFinishWith nested pid ready) := by
  apply CallbackQuiet.state_of_history
  intro before
  exact RetirementSecurity.NestedPeerRelease.rx_rxFinish_history
    (nested_quiet_history ρ disposal before) pid ready

theorem rx_finish_erases (pid : PeerId) (ready : Packets.RxReady) :
    ErasesStatePrefix (RetirementSecurity.NestedPeerRelease.rxFinishWith nested pid ready)
      (Packets.rxFinish pid ready) :=
  RetirementSecurity.NestedPeerRelease.rxFinishObserved_erases _ _ pid ready

theorem receive_quiet (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none) (msg : Key) (src : SkbSource) :
    CallbackQuiet.StateQuiet ρ (RetirementSecurity.NestedPeerRelease.receive nested msg src) := by
  apply CallbackQuiet.state_of_history
  intro before
  exact RetirementSecurity.NestedPeerRelease.receive_history
    (nested_quiet_history ρ disposal before) msg src

theorem receive_erases (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (RetirementSecurity.NestedPeerRelease.receive nested msg src) (wgReceive msg src) :=
  RetirementSecurity.NestedPeerRelease.receiveObserved_erases _ _ msg src


theorem flushed_clear_quiet (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none) (pid : PeerId) :
    CallbackQuiet.StateQuiet ρ (RetirementSecurity.NestedPeerRelease.flushedClearWith nested pid) := by
  apply CallbackQuiet.state_of_history
  intro before
  exact RetirementSecurity.NestedPeerRelease.flushedClear_history
    (nested_quiet_history ρ disposal before) pid

theorem flushed_clear_erases (pid : PeerId) :
    ErasesStatePrefix (RetirementSecurity.NestedPeerRelease.flushedClearWith nested pid)
      (runFlushedClearWork pid) := by
  simpa only [RetirementSecurity.NestedPeerRelease.flushedClear_native] using
    RetirementSecurity.NestedPeerRelease.flushedClear_erases
      (RetirementSecurity.NestedPeerRelease.observedOps_erases _ _) pid

theorem clear_worker_quiet (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none) :
    CallbackQuiet.ProductQuiet ρ (Driver.clearWorkerObserved hooks) :=
  CallbackQuiet.clear_worker ρ disposal

theorem clear_worker_erases : ErasesPrefix (Driver.clearWorkerObserved hooks) Env.runOneClearWorker :=
  RetirementSecurity.NestedPeerRelease.oneClearObserved_erases _ _

theorem dump_dispatch_quiet (ρ : Event → Option F)
    (disposal : ∀ event, ρ (.stagedDisposal event) = none) (call : Syscall) :
    CallbackQuiet.ProductQuiet ρ (RetirementSecurity.NestedPeerRelease.dumpDispatch nested call) :=
  CallbackQuiet.dump_dispatch ρ disposal call

theorem dump_dispatch_erases (call : Syscall) :
    ErasesPrefix (RetirementSecurity.NestedPeerRelease.dumpDispatch nested call) (Leanux.dispatch call) :=
  RetirementSecurity.NestedPeerRelease.dumpDispatchObserved_erases _ _ call

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackFrames
