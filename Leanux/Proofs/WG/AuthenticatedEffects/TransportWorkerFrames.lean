import Leanux.Proofs.WG.AuthenticatedEffects.TransportHookFrames

/-! Actual TX encryption and deferred handshake sending preserve the live
receive packet carrier. Checksums retain their native product-world frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportHookFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransportCarrier
set_option maxHeartbeats 600000

theorem wg (action : WG.M α) (same : SameView RxDisposition.nativeRxStore action) :
    SameView RxDisposition.rxStore (liftWG action) :=
  sameView_liftWG _ _ action same (fun _ _ _ eq => eq)

theorem ambient (action : AmbientM α) :
    SameView RxDisposition.rxStore (monadLift action : Leanux.M α) :=
  fun _ => productAmbient_spec action _ (fun _ _ hi => hi)

theorem encryptPacket (kid : KeypairId) (pkt : DataPacket) :
    SameView RxDisposition.rxStore (WG.encryptPacket Env.checksumHelp kid pkt) := by
  intro initial
  let P := fun w => RxDisposition.rxStore w = initial
  change Preserves P _
  have clock {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    (ambient a).wp (· = initial)
  have padding : Preserves P (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    (wg _ ((calculateSkbPadding_sameWGWorld _ _).factor RxDisposition.nativeRxStore)).wp (· = initial)
  have checksum (p : Packet) : Preserves P (Env.checksumHelp p) := (checksumHelp_sameWorld p).wp P
  have key : Preserves P (monadLift (getKeypair kid) : Leanux.M Keypair) :=
    (wg _ (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.readKey) kid).factor Prod.snd)).wp (· = initial)
  routing_tx_source [WG.encryptPacket] using [clock,padding,checksum,key]

theorem encrypt (item : Option (List SkbId)) :
    SameView RxDisposition.rxStore (RxWorkers.encryptStepTailSource item) := by
  intro initial
  let P := fun w => RxDisposition.rxStore w = initial
  change Preserves P _
  have clock {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    (ambient a).wp (· = initial)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    (wg _ (getTxSkb_rx id)).wp (· = initial)
  have write (id : SkbId) (f : DataPacket → DataPacket) : Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    (wg _ ((RxCredits.setTx_protect id f).factor (fun v => v.2.1))).wp (· = initial)
  have publish (xs : List SkbId) (state : PacketState) : Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    (wg _ (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.enqueuePeer_geometry) xs state).factor Prod.snd)).wp (· = initial)
  have packet (kid : KeypairId) (pkt : DataPacket) : Preserves P (WG.encryptPacket Env.checksumHelp kid pkt) :=
    (encryptPacket kid pkt).wp (· = initial)
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,publish,packet,clock]

theorem sendWorker : SameView RxDisposition.rxStore Env.runOneSendWorker := by
  unfold Env.runOneSendWorker
  apply SameView.bind (wg _ (TransportPublication.store_rx _ getDev_sameWGStore))
  intro d
  cases d.sendWorkQueue.head? with
  | none => exact ambient (AmbientM.invariant _)
  | some head =>
    dsimp only
    apply SameView.bind (ambient (AmbientM.peekUnit .sendWorker))
    intro unit
    cases unit <;> dsimp only
    all_goals apply SameView.bind
    · exact SameView.pure _ _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact wg _ ((TransportRemoval.flushedSend_geometry pid).factor Prod.snd)
    · exact ambient (AmbientM.resolveUnit _ _ _)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact wg _ ((TransportRemoval.flushedSend_geometry pid).factor Prod.snd)

end Leanux.Proofs.WG.AuthenticatedEffects.TransportHookFrames
