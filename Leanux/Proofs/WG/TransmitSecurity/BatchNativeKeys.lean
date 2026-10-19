import Leanux.Proofs.WG.TransmitSecurity.BatchNativeFrames

/-! Native key maintenance preserves queued batches' selected peer/key words.
These frames do not assert that key objects survive a final reference release. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem wire {action : WG.M α} (queues : SameView handoffTxView action)
    (packets : SameView txCryptWire action) : Preserves Inv action :=
  frame (pair queues (PacketMaterial.of_packets (packets.factor Prod.snd)))

theorem handshake_zero (pid : PeerId) : Preserves Inv (handshakeZero pid) :=
  wire (OccurrenceKeys.handshake_zero_queues pid) (OccurrenceKeys.handshake_zero_wire pid)

theorem handshake_clear (pid : PeerId) : Preserves Inv (handshakeClear pid) :=
  wire (OccurrenceKeys.handshake_clear_queues pid) (OccurrenceKeys.handshake_clear_wire pid)

theorem clear (pid : PeerId) : Preserves Inv (keypairsClear pid) :=
  wire (OccurrenceKeys.clear_queues pid) (OccurrenceKeys.clear_wire pid)

theorem expire (pid : PeerId) : Preserves Inv (expireCurrentPeerKeypairs pid) :=
  wire (OccurrenceKeys.expire_queues pid) (OccurrenceKeys.expire_wire pid)

theorem create (owner : Option PeerId) : Preserves Inv (keypairCreate owner) :=
  wire (OccurrenceKeys.create_queues owner) (OccurrenceKeys.create_wire owner)

theorem rotate (pid : PeerId) (kid : KeypairId) : Preserves Inv (addNewKeypair pid kid) :=
  wire (OccurrenceKeys.rotate_queues pid kid) (OccurrenceKeys.rotate_wire pid kid)

theorem derive (kid : KeypairId) (initiator : Bool) (chain : List UInt8) : Preserves Inv (deriveKeys kid initiator chain) :=
  wire (OccurrenceKeys.derive_queues kid initiator chain) (OccurrenceKeys.derive_wire kid initiator chain)

theorem session (pid : PeerId) : Preserves Inv (beginSession pid) :=
  wire (OccurrenceKeys.session_queues pid) (OccurrenceKeys.session_wire pid)

theorem create_initiation (pid : PeerId) : Preserves Inv (createInitiation pid) :=
  wire (OccurrenceKeys.create_initiation_queues pid) (OccurrenceKeys.create_initiation_wire pid)

theorem create_response (pid : PeerId) : Preserves Inv (createResponse pid) :=
  wire (OccurrenceKeys.create_response_queues pid) (OccurrenceKeys.create_response_wire pid)

theorem add_mac (pid : PeerId) (message : List UInt8) : Preserves Inv (addMacToPacket pid message) :=
  wire (OccurrenceKeys.add_mac_queues pid message) (OccurrenceKeys.add_mac_wire pid message)

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
