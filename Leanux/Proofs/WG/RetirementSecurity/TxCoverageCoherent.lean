import Leanux.Proofs.WG.RetirementSecurity.TxCoverageDeferred
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeviceConfiguration

/-! Resident coverage joins the existing initialized physical inventory. The
allocation companion supplies vacancy at peer creation; this is a state-only
conjunction and does not infer journal event chronology from erasure. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCovered
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits

def Inv (locals : List TxLocalBatch) (active : List (List SkbId)) (w : WGWorld) : Prop :=
  OccurrenceStack.Ready locals active w ∧ TxCoverage locals w

theorem join {action : WG.M α}
    (physical : Preserves (OccurrenceStack.Ready locals active) action)
    (coverage : Preserves (TxCoverage locals) action) : Preserves (Inv locals active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp physical w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp coverage w a result v b before.2 run⟩

theorem product_join {action : Leanux.M α}
    (physical : Preserves (fun w:World=>OccurrenceStack.Ready locals active w.wg) action)
    (coverage : Preserves (fun w:World=>TxCoverage locals w.wg) action) :
    Preserves (fun w:World=>Inv locals active w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact ⟨(hoare_iff_run _ _ _).mp physical w result v before.1 run,
    (hoare_iff_run _ _ _).mp coverage w result v before.2 run⟩

theorem ready_store (same : wgStoreView v=wgStoreView w)
    (before : Inv locals active w) : Inv locals active v :=
  ⟨OccurrenceStack.ready_store same before.1,TxCoverageStack.ready_store same before.2⟩

theorem product_store {action : Leanux.M α} (frame : SameProductStore action) :
    Preserves (fun w:World=>Inv locals active w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact ready_store (congrArg (fun s : ProductStore43=>s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w result v run)) before

namespace Native
open TxCoverageNative

theorem coherent_store {action : WG.M α} (same : SameWGStore action) : Preserves (Inv locals active) action :=
  join (RxPollOccurrences.store same) (TxCoverageNative.store same)

theorem peer_update (pid : PeerId) (f : Peer→Peer)
    (stamp : ∀p,(f p).internalId=p.internalId)
    (queue : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (Inv locals active) (getPeer pid >>= fun p=>setPeer pid (f p)) :=
  join (OccurrenceHandshake.peer_update pid f stamp queue) (TxCoverageNative.peer_update pid f queue)

theorem peer_update_bind (pid : PeerId) (f : Peer→Peer) (tail : Unit→WG.M α)
    (stamp : ∀p,(f p).internalId=p.internalId)
    (queue : ∀p,(f p).txQueue.all=p.txQueue.all)
    (next : ∀x,Preserves (Inv locals active) (tail x)) :
    Preserves (Inv locals active) (getPeer pid >>= fun p=>setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (peer_update pid f stamp queue) next

theorem modify_device (f : Device→Device)
    (identities : ∀w,identityView {w with dev:=w.dev.map f}=identityView w)
    (metadata : ∀w,allocationMetadata {w with dev:=w.dev.map f}=allocationMetadata w)
    (wire : ∀w,txCryptWire {w with dev:=w.dev.map f}=txCryptWire w)
    (queues : ∀w,handoffTxView {w with dev:=w.dev.map f}=handoffTxView w) :
    Preserves (Inv locals active) (modifyDev f) := by
  apply join (OccurrenceHandshake.modify_device f identities metadata wire queues)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases run
  apply before.cells (congrArg Prod.snd (wire w))
  exact congrArg (fun q=>fun pid=>(q pid).getD []) (queues w)

theorem peer_put (pid : Option PeerId) : Preserves (Inv locals active) (peerPut pid) :=
  join (RxPollOccurrences.peer_put pid) (TxCoverageNative.peer_put pid)

theorem peer_get (pid : PeerId) : Preserves (Inv locals active) (peerGet pid) :=
  join (OccurrenceTimers.peer_get pid) (TxCoverageNative.peer_get pid)

theorem staged (pid : PeerId) : Preserves (Inv locals active) (sendStagedPackets pid) :=
  join (OccurrenceConfiguration.staged pid) (TxCoverageNative.staged pid)

theorem keepalive (pid : PeerId) : Preserves (Inv locals active) (sendKeepalive pid) :=
  join (OccurrenceHandshake.keepalive pid) (TxCoverageNative.keepalive pid)

theorem maintenance (call : MaintenanceCall) : Preserves (Inv locals active) call.original :=
  join (OccurrenceTimers.maintenance call) (TxCoverageNative.maintenance call)

theorem clear_endpoint (pid : PeerId) : Preserves (Inv locals active) (clearPeerEndpointSrc pid) :=
  join (OccurrenceTimers.clear_endpoint pid) (TxCoverageNative.clear_endpoint pid)

macro "tx_covered_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply peer_update <;> intro p <;> rfl)
  | (receive_update_head Bind.bind
     apply peer_update_bind
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact coherent_store getDev_sameWGStore)
  | (rx_retention_head modifyDev
     apply modify_device
     · intro w; unfold identityView Peers.snapshot keypairResidents packetResidents; simp [Option.bind_map,Function.comp_def]
     · intro w; simp [allocationMetadata,deviceAllocationMetadata,Option.map_map,Function.comp_def] <;> rfl
     · intro w; simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,Option.map_map,Option.bind_map,Function.comp_def]
     · intro w; funext pid; simp [handoffTxView,Option.bind_map,Function.comp_def])
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | rxstack_preserves_join
  | rx_retention_step)

end Native
end Leanux.Proofs.WG.RetirementSecurity.TxCovered
