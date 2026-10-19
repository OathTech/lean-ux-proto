import Leanux.Proofs.WG.TransmitSecurity.NonceScheduler
import Leanux.Proofs.WG.TransmitSecurity.NonceTimers
import Leanux.Proofs.WG.Origins.RetainingLifecycle
import Leanux.Proofs.Framing.EnvLeaves

/-! Nonce frames at native deferred-worker and wheel bookkeeping sites.
The clear worker may erase a resident cell; it cannot reset a retained one. -/
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem send_initiation (pid : PeerId) : SameView view (sendHandshakeInitiation pid) :=
  full (Origins.Retaining.sendHandshakeInitiation_material pid)
    (Keypairs.WGTransitions.sendHandshakeInitiation_sameSnapshot pid)

theorem send_worker (pid : PeerId) : SameView view (handshakeSendWorker pid) :=
  (send_initiation pid).bind (fun _ => peerPut (some pid))

theorem clear_handshake (pid : PeerId) : SameView view (handshakeClear pid) :=
  full (Origins.Retaining.handshakeClear_material pid)
    (Keypairs.WGTransitions.handshakeClear_sameSnapshot pid)

theorem clear_worker (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (queuedExpiredZeroKeyMaterial pid) :=
  preserves_bind (native_frame h (clear_handshake pid)) (fun _ =>
    preserves_bind (clear pid h) (fun _ => native_frame h (peerPut (some pid))))

theorem stored {α : Type} {a : Leanux.M α} (frame : SameProductStore a) :
    PrefixPreserves (fun h (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.nodup) product_store frame

theorem wg_read : PrefixPreserves (fun h (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix getWG) :=
  stored (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    PrefixPreserves (fun h (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix (modifyWG f)) :=
  stored (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : PrefixPreserves (fun h (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix getEnv) := by
  apply product_lift
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  cases hr
  exact hi

theorem drained (what : String) (queues : List Bool) : SameProductStore (Env.requireDrained what queues) :=
  requireDrained_sameKernel what queues

theorem run_worker (worker : Worker) {body : Leanux.M Unit}
    (safe : ∀ h, Preserves (fun w : World => Inv (view w.wg) h) body) (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) (Env.runWorker worker body) := by
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Inv (view w.wg) h) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  have bodySafe := safe h
  routing_tx_source [Env.runWorker] using [bodySafe, ambient]
  all_goals exact ambient _

theorem one_send (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) Env.runOneSendWorker := by
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Inv (view w.wg) h) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  have read : Preserves (fun w : World => Inv (view w.wg) h) (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product _ _ (native_frame h device_read)
  have peer (pid : PeerId) : Preserves (fun w : World => Inv (view w.wg) h)
      (monadLift (getPeer pid) : Leanux.M Peer) :=
    PublicationPoll.native_product _ _ (native_frame h (peer_read pid))
  have write (pid : PeerId) (p : Peer) : Preserves (fun w : World => Inv (view w.wg) h)
      (monadLift (setPeer pid p) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (native_frame h (peer_write pid p))
  have edit (pid : PeerId) :
      Preserves (fun w : World => Inv (view w.wg) h)
        (monadLift (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (native_frame h (update
      (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) (fun _ => rfl)))
  have worker (pid : PeerId) := run_worker .sendWorker
    (fun h => PublicationPoll.native_product _ _ (native_frame h (send_worker pid))) h
  routing_tx_source [Env.runOneSendWorker] using [worker,read,peer,write,edit,ambient]
  all_goals first | exact worker _ | exact ambient _

theorem one_clear (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) Env.runOneClearWorker := by
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Inv (view w.wg) h) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  have read : Preserves (fun w : World => Inv (view w.wg) h) (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product _ _ (native_frame h device_read)
  have edit (pid : PeerId) :
      Preserves (fun w : World => Inv (view w.wg) h)
        (monadLift (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (native_frame h (update
      (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) (fun _ => rfl)))
  have worker (pid : PeerId) := run_worker .clearPeerWorker
    (fun h => PublicationPoll.native_product _ _ (clear_worker pid h)) h
  routing_tx_source [Env.runOneClearWorker] using [worker,read,edit,ambient]
  all_goals first | exact worker _ | exact ambient _

theorem step_complete (b : UInt64) : SameProductStore (Env.requireStepComplete b) := by
  unfold Env.requireStepComplete
  apply SameView.bind (liftWG_sameProductStore _ getDev_sameWGStore)
  intro d
  split
  · exact fun _ => hoare_throw _
  · exact SameView.pure _ _

theorem nothing_due (j : UInt64) : SameProductStore (Env.requireNothingDue j) := by
  intro initial
  let P := fun w => productStoreView w = initial
  have read : Preserves P getWG := productGetWG_spec (· = initial)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have look (w : Worker) (u : Nat) : Preserves P (Env.sectionAppearsLater w u) := by
    apply (hoare_iff_run _ _ _).mpr
    intro v result z hi hr
    cases hr
    exact hi
  have timer (t : PeerTimer) : Preserves P (Env.timerWorker t) :=
    (timerWorker_sameKernel t).wp (· = initial)
  have stop {α : Type} (e : Stop) : Preserves P (throw e : Leanux.M α) := hoare_throw e
  change Preserves P _
  routing_tx_source [Env.requireNothingDue] using [read,ambient,look,timer,stop]

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
