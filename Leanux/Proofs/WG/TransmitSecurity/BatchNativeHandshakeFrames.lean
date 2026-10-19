import Leanux.Proofs.WG.TransmitSecurity.BatchNativeKeepalive

/-! Handshake consumption and sending preserve every queued packet's selected
peer/key words. Empty-peer retirement is allowed by the content projection. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem consume_initiation (message : List UInt8) : Preserves Inv (consumeInitiation message) :=
  contents_wire (OccurrenceHandshake.consume_initiation_contents message)
    (OccurrenceHandshake.consume_initiation_wire message)

theorem consume_response (message : List UInt8) : Preserves Inv (consumeResponse message) :=
  contents_wire (OccurrenceHandshake.consume_response_contents message)
    (OccurrenceHandshake.consume_response_wire message)

theorem consume_cookie (message : List UInt8) : Preserves Inv (cookieMessageConsume message) :=
  contents_wire (OccurrenceHandshake.cookie_consume_contents message)
    (OccurrenceHandshake.cookie_consume_wire message)

theorem send_buffer (pid : PeerId) (message : List UInt8) : Preserves Inv (sendBufferToPeer pid message) :=
  contents_wire (OccurrenceHandshake.buffer_contents pid message) (OccurrenceHandshake.buffer_wire pid message)

theorem send_response (pid : PeerId) : Preserves Inv (sendHandshakeResponse pid) :=
  contents_wire (OccurrenceHandshake.send_response_contents pid) (OccurrenceHandshake.send_response_wire pid)

theorem send_initiation (pid : PeerId) : Preserves Inv (sendHandshakeInitiation pid) :=
  contents_wire (OccurrenceHandshake.send_initiation_contents pid) (OccurrenceHandshake.send_initiation_wire pid)

theorem send_worker (pid : PeerId) : Preserves Inv (handshakeSendWorker pid) :=
  contents_wire (OccurrenceHandshake.send_worker_contents pid) (OccurrenceHandshake.send_worker_wire pid)

theorem derived (pid : PeerId) : Preserves Inv (timersSessionDerived pid) :=
  contents_wire (OccurrenceHandshake.derived_contents pid) (OccurrenceHandshake.derived_wire pid)

theorem initiated (pid : PeerId) : Preserves Inv (timersHandshakeInitiated pid) :=
  contents_wire (OccurrenceHandshake.initiated_contents pid) (OccurrenceHandshake.initiated_wire pid)

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
