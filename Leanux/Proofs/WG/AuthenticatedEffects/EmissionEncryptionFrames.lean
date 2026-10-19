import Leanux.Proofs.WG.AuthenticatedEffects.EmissionStagingFrames
import Leanux.Proofs.WG.TransmitSecurity.EmissionOuterFrames

/-! Native encryption and publication update packet bytes and scheduling.
Neither appends a datagram before the actual completion socket callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem packet (kid : KeypairId) (pkt : DataPacket) :
    SameView EmissionOuter.Sent (encryptPacket Env.checksumHelp kid pkt) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have clock {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have padding : Preserves P (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    EmissionOuter.wg _ ((calculateSkbPadding_sameWGWorld _ _).factor WGWorld.sent) initial
  have checksum (p : Packet) : Preserves P (Env.checksumHelp p) := (checksumHelp_sameWorld p).wp P
  have key : Preserves P (monadLift (getKeypair kid) : Leanux.M Keypair) :=
    EmissionOuter.wg _ (fun sent => getKeypair_sent_spec (· = sent) kid) initial
  routing_tx_source [encryptPacket] using [clock,padding,checksum,key]

theorem encrypt_tail (item : Option (List SkbId)) : SameView EmissionOuter.Sent (RxWorkers.encryptStepTailSource item) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have clock {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    EmissionOuter.wg _ (fun sent => skb_sent_spec (· = sent) _) initial
  have write (id : SkbId) (f : DataPacket → DataPacket) : Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    EmissionOuter.wg _ (fun sent => skb_sent_spec (· = sent) _) initial
  have publish (items : List SkbId) (state : PacketState) : Preserves P (monadLift (enqueuePerPeerTx items state) : Leanux.M Unit) :=
    EmissionOuter.wg _
      ((pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.EmissionStagingFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames.enqueue_peer) items state) initial
  have crypt (kid : KeypairId) (pkt : DataPacket) : Preserves P (encryptPacket Env.checksumHelp kid pkt) := packet kid pkt initial
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,publish,crypt,clock]

theorem ring_poll : SameView WGWorld.sent TxRing.pollSource := by
  sent_frame [TxRing.pollSource] using []

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
