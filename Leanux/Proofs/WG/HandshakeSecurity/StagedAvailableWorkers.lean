import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableEffects
import Leanux.Proofs.WG.TransmitSecurity.StagedWorkerFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedCompletionFrames

/-! Native packet-store, crypt worker and TX completion leaves retain the
available staged births. These facts do not add an allocation receipt. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem skb (action : SkbM α) : Preserves (Inv h) (liftSkb action) := by
  apply hoare_liftSkb
  intro w d packets before device
  apply before.retains
  · simp only [Packets.epoch,device,Option.map_some]
  · intro pid cell found
    simpa only [stagedAt,device,Option.bind_some] using found

theorem counter (kid : KeypairId) (nonce : Nat) : Preserves (Inv h) (counterValidate kid nonce) := by
  unfold counterValidate
  simp (config := {zeta := false}) only [WG.orM,branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head setKeypair; exact write_key _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv h)
       intro x b
       change Preserves (Inv h) _)
    | staged_available_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem poll : Preserves (Inv h) TxRing.pollSource := by
  unfold TxRing.pollSource
  repeat' staged_available_native

theorem publish_tx (items : List SkbId) (state : PacketState) :
    Preserves (Inv h) (enqueuePerPeerTx items state) :=
  frame (PacketOrigins.epoch_ring (TxRing.enqueuePeer_frame items state)) (Staged.publish items state)

theorem decrypt (packet : RxPacket) : Preserves (Inv h) (decryptPacket packet) := by
  unfold decryptPacket hiddenAlloc
  repeat' first
    | (rx_retention_head setKeypair; exact write_key _ _)
    | staged_available_native

private theorem publish_rx_staged (id : SkbId) (state : PacketState) :
    SameView stagedAt (RxWorkers.publishSource id state) := by
  intro initial
  unfold RxWorkers.publishSource
  apply preserves_bind ((Exact.skb _).wp (· = initial))
  intro packet
  apply preserves_bind (indexOwner_peerDeref_preserves _ _)
  intro pid
  apply preserves_bind ((Exact.peer_get pid).wp (· = initial))
  intro _
  apply hoare_bind _ _ (Staged.read_saved (· = initial) pid)
  intro peer
  have tail : Hoare
      (do setRxSkb id fun q => {q with state}; setPeer pid {peer with napiScheduled := true}; pure pid)
      (fun w => stagedAt w = initial ∧ stagedAt w pid = some (peer.internalId,peer.staged))
      (fun _ w => stagedAt w = initial) := by
    apply hoare_bind _ _ ((Exact.skb _).wp (fun q => q = initial ∧ q pid = some (peer.internalId,peer.staged)))
    intro _
    apply hoare_bind _ _ (Staged.write_saved (· = initial) pid {peer with napiScheduled := true})
    intro _
    exact preserves_pure pid
  split
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b before run
    cases run
  · exact tail

theorem publish_rx (id : SkbId) (state : PacketState) :
    Preserves (Inv h) (RxWorkers.publishSource id state) :=
  frame (PacketOrigins.epoch_ring ((RetirementSecurity.OccurrenceDecrypt.publish_wire id state).factor Prod.fst))
    (Staged.of_view _ (publish_rx_staged id state))

theorem decrypt_prepare : Preserves (Inv h) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  repeat' first
    | (rx_retention_head decryptPacket; exact decrypt _)
    | (rx_retention_head RxWorkers.publishSource; exact publish_rx _ _)
    | (rx_retention_head getRxSkb; exact skb _)
    | (rx_retention_head setRxSkb; exact skb _)
    | staged_available_native

theorem product (action : WG.M α) (safe : Preserves (Inv h) action) :
    Preserves (fun w : World => Inv h w.wg) (liftWG action) :=
  PublicationPoll.native_product (Inv h) action safe

private theorem packet (kid : KeypairId) (pkt : DataPacket) (h : List AuthenticatedEffects.CausalJournal.Event) :
    Preserves (fun w : World => Inv h w.wg) (encryptPacket Env.checksumHelp kid pkt) := by
  let P := fun w : World => Inv h w.wg
  change Preserves P _
  have clock {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    product _ ((calculateSkbPadding_sameWGWorld _ _).wp (Inv h))
  have checksum (p : Packet) : Preserves P (Env.checksumHelp p) := (checksumHelp_sameWorld p).wp P
  have key : Preserves P (monadLift (getKeypair kid) : Leanux.M Keypair) := product _ (read_key kid)
  routing_tx_source [encryptPacket] using [clock,padding,checksum,key]

theorem encrypt (item : Option (List SkbId)) (h : List AuthenticatedEffects.CausalJournal.Event) :
    Preserves (fun w : World => Inv h w.wg) (RxWorkers.encryptStepTailSource item) := by
  let P := fun w : World => Inv h w.wg
  change Preserves P _
  have clock {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) := product _ (skb _)
  have write (id : SkbId) (f : DataPacket → DataPacket) : Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) := product _ (skb _)
  have publish (items : List SkbId) (state : PacketState) : Preserves P (monadLift (enqueuePerPeerTx items state) : Leanux.M Unit) :=
    product _ (publish_tx items state)
  have crypt (kid : KeypairId) (pkt : DataPacket) : Preserves P (encryptPacket Env.checksumHelp kid pkt) := packet kid pkt h
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,publish,crypt,clock]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000

theorem drop_completion (pid : PeerId) : Preserves (Inv h)
    (do setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}) := by
  rw [getPeer_twice]
  repeat' staged_available_native

theorem dispose_completion (pid : PeerId) (items : List SkbId) (key : KeypairId) :
    Preserves (Inv h) (TxDisposition.disposeSource pid items key) := by
  unfold TxDisposition.disposeSource
  repeat' first
    | (rx_retention_head freeTxSkb; exact skb _)
    | (rx_retention_head keypairPut; exact key_put _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv h)
       intro id state
       change Preserves (Inv h) _)
    | staged_available_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
