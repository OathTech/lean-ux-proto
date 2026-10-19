import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationDeviceBoundary
import Leanux.Proofs.WG.Queues.DeviceStages

/-! Device-configuration frames keep the exact peer account alongside the
existing structural and configured-identity projections. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ConfigurationDevice
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders Configuration ConfigurationDeviceBoundary

def fields (w : WGWorld) :=
  (HolderEncrypt.fields w,BaseCoherence.view w,ConfiguredIdentity.view w)

theorem fields_keeps (same : fields v=fields w) (hi : Entry cs loans w) : Entry cs loans v :=
  ⟨ExactBoundary.fields hi.1 (congrArg Prod.fst same),
    BaseCoherence.transport hi.2.1 (congrArg (fun s => s.2.1) same),
    fun s hs => hi.2.2 s ((congrArg (fun s => s.2.2) same).symm.trans hs)⟩

theorem frame {action : WG.M α} (same : SameView fields action) :
    Preserves (Entry cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact fields_keeps ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run) hi

theorem join {action : WG.M α}
    (account : Preserves (ExactBoundary cs loans) action)
    (coherent : Preserves BaseCoherence.Inv action)
    (configured : Preserves ConfiguredIdentity.Inv action) : Preserves (Entry cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp account w a result v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp coherent w a result v b hi.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp configured w a result v b hi.2.2 run⟩

theorem base_frame {action : WG.M α} (same : SameView BaseCoherence.view action) :
    Preserves BaseCoherence.Inv action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact BaseCoherence.transport hi ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem store {action : WG.M α} (same : SameWGStore action) :
    Preserves (Entry cs loans) action :=
  frame (same.of_factor (fun s : WGStoreView => fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}) _ (fun _ => rfl))

theorem configuration {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Entry cs loans) action := by
  apply frame
  apply same.of_factor (fun s : WGOwnedView => fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8})
  intro w
  unfold fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows ConfiguredIdentity.view ConfiguredIdentity.state
  cases hd:w.dev <;> simp [configurationView,configurationDevice,wgOwnedView,wgStoreView,hd,rxView]

theorem socket {action : WG.M α} (same : SameSocket action) :
    Preserves (Entry cs loans) action := by
  apply frame
  apply same.of_factor (fun s : WGOwnedView => fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8})
  intro w
  unfold fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows ConfiguredIdentity.view ConfiguredIdentity.state
  cases hd:w.dev <;> simp [socketView,socketDevice,wgOwnedView,wgStoreView,hd,rxView]

theorem readPeer (pid : PeerId) : Preserves (Entry cs loans) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  exact (getPeer_normal pid w v p a b run).1 ▸ hi

theorem modifyDevice (f : Device → Device)
    (same : ∀ w, fields {w with dev:=w.dev.map f}=fields w) :
    Preserves (Entry cs loans) (modifyDev f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases run
  exact fields_keeps (same w) hi

theorem modifyPeer (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p,(f p).internalId=p.internalId) (count : ∀ p,(f p).refcount=p.refcount)
    (rx : ∀ p,(f p).rxQueue=p.rxQueue) (napi : ∀ p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀ p k,(f p).keypairCurrent=some k → p.keypairCurrent=some k)
    (tx : ∀ p,(f p).txQueue.all=p.txQueue.all)
    (identity : ∀ p,ConfiguredIdentity.cell (f p)=ConfiguredIdentity.cell p) :
    Preserves (Entry cs loans) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply join
  · exact TimerFrames.modify_boundary
      pid f stamp count rx napi current tx
  · apply base_frame
    exact ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_read) pid).bind
      (fun p => (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_write) pid (f p))
  · exact ConfiguredRemoval.frame (ConfiguredIdentity.modifyPeer_view pid f identity)

theorem modifyPeerThen (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (stamp : ∀ p,(f p).internalId=p.internalId) (count : ∀ p,(f p).refcount=p.refcount)
    (rx : ∀ p,(f p).rxQueue=p.rxQueue) (napi : ∀ p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀ p k,(f p).keypairCurrent=some k → p.keypairCurrent=some k)
    (tx : ∀ p,(f p).txQueue.all=p.txQueue.all)
    (identity : ∀ p,ConfiguredIdentity.cell (f p)=ConfiguredIdentity.cell p)
    (next : ∀ x, Preserves (Entry cs loans) (tail x)) :
    Preserves (Entry cs loans) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (modifyPeer pid f stamp count rx napi current tx identity) next

macro "retired_device_entry_step" : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply modifyPeer
     all_goals first | (intro p; rfl) | (intro p k h; exact h))
  | (receive_update_head Bind.bind
     apply modifyPeerThen
     all_goals first | (intro p; rfl) | (intro p k h; exact h) | skip
     intro x)
  | (rx_retention_head getPeer; exact readPeer _)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev
     apply modifyDevice
     intro w
     unfold fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
     unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
     unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows ConfiguredIdentity.view ConfiguredIdentity.state
     cases hd:w.dev <;> simp [hd,rxView])
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Entry _ _)
     intro x b
     change Preserves (Entry _ _) _)
  | rx_retention_step)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ConfigurationDevice
