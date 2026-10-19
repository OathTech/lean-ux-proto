import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase

/-! Native nested release and terminal observers preserve a history property
when their actual access and receipt events preserve it. No state carrier is
inferred from an unchanged event projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackHistory
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues
open HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

variable {Safe : List Event → Prop}

theorem state_receipt (body : WGPrefix Event α) (safe : Driver.StateHistorySafe Safe body)
    (record : WGRunWitness α → Event)
    (emits : ∀ r, Driver.StateHistorySafe Safe (emitStatePrefix (record r))) :
    Driver.StateHistorySafe Safe (receiptWGObserved body record) := by
  unfold receiptWGObserved
  exact Driver.History.state_bind safe.captureWGObserved (fun r =>
    Driver.History.state_bind (emits r) (fun _ => Driver.History.state_pure _))

theorem product_receipt (body : PrefixM Event α) (safe : Driver.ProductHistorySafe Safe body)
    (record : RunWitness α → Event)
    (emits : ∀ r, Driver.ProductHistorySafe Safe (emitPrefix (record r))) :
    Driver.ProductHistorySafe Safe (receiptObserved body record) := by
  unfold receiptObserved
  exact Driver.History.product_bind safe.captureObserved (fun r =>
    Driver.History.product_bind (emits r) (fun _ => Driver.History.product_pure _))

theorem peer (encode : Peers.PeerEvent → Event) (decode : Event → Option Peers.PeerEvent)
    (quiet : ∀ {α} (body : WGPrefix Peers.PeerEvent α),
      Driver.StateHistorySafe Safe (focusStatePrefix encode decode body))
    (emits : ∀ event, Driver.StateHistorySafe Safe (emitStatePrefix (.stagedDisposal event)))
    (pid : Option PeerId) :
    Driver.StateHistorySafe Safe (PeerSource.observed
      (PeerSource.Ops.focus encode decode PeerSource.peers) Event.stagedDisposal pid) := by
  unfold PeerSource.observed PeerSource.cutWith
  simp only [PeerSource.Ops.focus,PeerSource.peers]
  repeat' first
    | (driver_history_head receiptWGObserved; refine state_receipt _ ?_ _ (fun r => emits _))
    | (driver_history_head focusStatePrefix; exact quiet _)
    | driver_state_history_step

theorem lifetime_put
    (quiet : ∀ {α} (body : WGPrefix Peers.PeerEvent α), Driver.StateHistorySafe Safe
      (focusStatePrefix (LifetimeSource.peerEncode (Event.old ∘ Journal.completionEvent))
        (LifetimeSource.peerDecode completion?) body))
    (emits : ∀ event, Driver.StateHistorySafe Safe (emitStatePrefix (.stagedDisposal event)))
    (pid : Option PeerId) : Driver.StateHistorySafe Safe (completionLifetime.put pid) :=
  peer _ _ quiet emits pid

theorem tx_dispose
    (quiet : ∀ {α} (body : PrefixM TxDisposition.Event α),
      Driver.ProductHistorySafe Safe (focusPrefix txEvent txEvent? body))
    (release : ∀ peer, Driver.ProductHistorySafe Safe (TxSource.releaseObserved txEvent txEvent? Event.stagedDisposal peer))
    (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    Driver.ProductHistorySafe Safe (TxSource.dispose (TxSource.observed txEvent txEvent? Event.stagedDisposal) pid item key) := by
  unfold TxSource.dispose
  simp only [TxSource.observed,TxSource.Ops.focus]
  repeat' first
    | (driver_history_head TxSource.releaseObserved; exact release _)
    | (driver_history_head focusPrefix; exact quiet _)
    | driver_product_history_step

theorem dead
    (quiet : ∀ {α} (body : PrefixM TxDisposition.Event α),
      Driver.ProductHistorySafe Safe (focusPrefix txEvent txEvent? body))
    (release : ∀ peer, Driver.ProductHistorySafe Safe (TxSource.releaseObserved txEvent txEvent? Event.stagedDisposal peer))
    (emits : ∀ receipt, Driver.ProductHistorySafe Safe (emitPrefix (.terminalDrop receipt)))
    (pid : PeerId) (item : List SkbId) (head : DataPacket) :
    Driver.ProductHistorySafe Safe
      (Terminal.deadObserved txEvent txEvent? Event.stagedDisposal Event.terminalDrop pid item head) := by
  unfold Terminal.deadObserved Terminal.disposeWith Terminal.freeObserved Terminal.observed
  simp only [TxSource.observed,TxSource.Ops.focus]
  repeat' first
    | (driver_history_head TxSource.releaseObserved; exact release _)
    | (driver_history_head receiptObserved; refine product_receipt _ ?_ _ (fun r => emits _))
    | (driver_history_head focusPrefix; exact quiet _)
    | driver_product_history_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackHistory
