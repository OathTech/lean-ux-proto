import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionQuietH1

/-! The actual shared receive advances confirmation labels before its staging
and packet-delivery suffix. Quiet suffixes retain the consumed pending ticket
invariant on normal return and keep prior distinctness when they stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem staging (H1 : H1PendingQuietFrames) (pid : PeerId) :
    Observed (Driver.stagingObserved Responder.DriverCuts.hooks pid) :=
  quiet_native (staging_quiet pid) (staging_erases pid) (fun confirmed =>
    Carrier.bounds confirmed (ResidentMaterial.bounds_staging pid)
      (PendingPromotion.preserves (H1.staging pid) confirmed))

theorem keepalive_quiet (pid : PeerId) :
    LabelsQuiet (Driver.keepaliveObserved Responder.DriverCuts.hooks pid) :=
  fun initial => Driver.keepalive_history (quiet_hooks initial) pid

theorem keepalive_erases (pid : PeerId) :
    ErasesStatePrefix (Driver.keepaliveObserved Responder.DriverCuts.hooks pid) (sendKeepalive pid) := by
  apply native_via_nonce (Driver.keepalive_projects native_projection pid)
    (Driver.keepalive_projects NativeDriver.nonce_projection pid)
  rw [Driver.nonce_keepaliveObserved_eq]
  exact Nonce.keepaliveObserved_erases pid

theorem keepalive (H1 : H1PendingQuietFrames) (pid : PeerId) :
    Observed (Driver.keepaliveObserved Responder.DriverCuts.hooks pid) :=
  quiet_native (keepalive_quiet pid) (keepalive_erases pid) (fun confirmed =>
    Carrier.bounds confirmed
      (ResidentMaterial.bounds_join (ConfiguredTraffic.keepalive pid)
        ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive_slots) pid))
      (PendingPromotion.preserves (H1.keepalive pid) confirmed))

theorem receiveTail_quiet (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    LabelsQuiet (Driver.receiveTailObserved Responder.DriverCuts.hooks pid pkt confirmed) :=
  fun initial => Driver.receiveTail_history (quiet_hooks initial) pid pkt confirmed

theorem receiveTail_erases (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    ErasesStatePrefix (Driver.receiveTailObserved Responder.DriverCuts.hooks pid pkt confirmed)
      (Confirmation.afterConfirmation pid pkt confirmed) := by
  apply native_via_nonce (Driver.receiveTail_projects native_projection pid pkt confirmed)
    (Driver.receiveTail_projects NativeDriver.nonce_projection pid pkt confirmed)
  rw [Driver.nonce_receiveTailObserved_eq]
  exact Nonce.receiveTailObserved_erases pid pkt confirmed

theorem receiveTail_bounds (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    Preserves ResidentMaterial.Bounds (Confirmation.afterConfirmation pid pkt confirmed) := by
  unfold Confirmation.afterConfirmation
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .doneReceivedNew confirmed) _)
  intro newKey
  have rest : Preserves ResidentMaterial.Bounds (do
      match ← RxCredits.prepareRest pid pkt with
      | none => pure none
      | some ready => Packets.rxFinish pid ready) := by
    apply preserves_bind (ResidentMaterial.bounds_prepare pid pkt)
    intro ready
    cases ready with
    | none => exact preserves_pure _
    | some ready => exact ResidentMaterial.bounds_finish pid ready
  cases newKey with
  | false => exact rest
  | true =>
    exact preserves_bind (ResidentMaterial.bounds_complete pid .walltimeLastHandshakeData) (fun _ =>
      preserves_bind (ResidentMaterial.bounds_staging pid) (fun _ => rest))

theorem receive_tail (H1 : H1PendingQuietFrames) (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    Observed (Driver.receiveTailObserved Responder.DriverCuts.hooks pid pkt confirmed) :=
  quiet_native (receiveTail_quiet pid pkt confirmed) (receiveTail_erases pid pkt confirmed)
    (fun labels => Carrier.bounds labels (receiveTail_bounds pid pkt confirmed)
      (PendingPromotion.preserves (H1.receiveTail pid pkt confirmed) labels))

/-- Native promotion extends the distinct label list before any subsequent
timer, staged send or delivery call. Its receipt survives every later Stop. -/
theorem consume (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames)
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Observed (Driver.consumeObserved Responder.DriverCuts.hooks pid pkt ep) := by
  unfold Driver.consumeObserved
  apply StatePrefixEnsures.bind (native _ (fun labels => Carrier.bounds labels
    (ResidentMaterial.bounds_endpoint pid ep) (frame_preserves (quiet.endpoint pid ep) labels)))
  intro _
  apply StatePrefixEnsures.bind (confirmation_observed edges pid pkt.keypair)
  intro confirmed
  exact receive_tail quiet pid pkt confirmed

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
