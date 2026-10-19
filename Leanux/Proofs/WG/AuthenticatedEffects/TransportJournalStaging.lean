import Leanux.Proofs.WG.AuthenticatedEffects.TransportJournalBase
import Leanux.Proofs.WG.AuthenticatedEffects.TransportFrontFrames

/-! The actual journal callbacks carry authenticated RX packets through staged
transmit work. Other event families cannot forge a replay receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransportCarrier
open Journal

abbrev StateSafe (g : WGPrefix Journal.Event α) :=
  TransportCarrier.StateSafe (fun _ => True) Journal.origin? Journal.replay? g
abbrev ProductSafe (g : PrefixM Journal.Event α) :=
  TransportCarrier.ProductSafe (fun _ => True) Journal.origin? Journal.replay? g

theorem selection (pid : PeerId) : StateSafe (Journal.selection pid) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun _ => focusPrefix_other Event.responder responder? replay? (fun _ => rfl) _)
    (state_erases handshake? (Journal.HandshakeProjection.selection pid))
    (TransportHookFrames.selection pid)

theorem confirmation (pid : PeerId) (kid : KeypairId) : StateSafe (Journal.confirmation pid kid) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun _ => focusPrefix_other Event.responder responder? replay? (fun _ => rfl) _)
    (state_erases handshake? (Journal.HandshakeProjection.confirmation pid kid))
    (TransportHookFrames.confirmation pid kid)

theorem session (pid : PeerId) : StateSafe (Journal.session pid) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun _ => focusPrefix_other Event.responder responder? replay? (fun _ => rfl) _)
    (state_erases handshake? (Journal.HandshakeProjection.session pid))
    (TransportHookFrames.session pid)

theorem reserve (kid : KeypairId) : StateSafe (Journal.reserve kid) :=
  state_quiet ((StateAppends.focus _ _ _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun w => focusPrefix_other Event.nonce nonce? replay?
      (fun _ => rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl))
    (state_erases handshake? (Journal.HandshakeProjection.reserve kid))
    (TransportHookFrames.reserve kid)

theorem allocate (packets : List DataPacket) : StateSafe (Journal.allocate packets) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
    (state_erases handshake? (Journal.HandshakeProjection.allocate packets))
    (TransportHookFrames.allocate packets)

theorem lower_history {g : PrefixM Journal.Event α}
    (app : Appends g) (frame : HistoryFrame replay? g) :
    StateAppends (NativeAdapter.lower g) ∧ StateHistoryFrame replay? (NativeAdapter.lower g) := by
  constructor
  · intro w a h
    exact app (NativeAdapter.world w a) h
  · intro w a h
    exact frame (NativeAdapter.world w a) h

theorem create (pid : PeerId) (item : List SkbId) : StateSafe (Journal.create pid item) :=
  state_quiet (lower_history (Appends.focus _ _ _)
    (focusPrefix_other Event.disposition disposition? replay? (fun _ => rfl) _)).1
    (lower_history (Appends.focus _ _ _)
      (focusPrefix_other Event.disposition disposition? replay? (fun _ => rfl) _)).2
    (state_erases handshake? (Journal.HandshakeProjection.create pid item))
    (TransportHookFrames.create pid item)

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Journal.front family addr packets mtu) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
    (state_erases handshake? (Journal.HandshakeProjection.front family addr packets mtu))
    (TransportHookFrames.front family addr packets mtu)

theorem armTimer (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (Journal.hooks.armTimer pid timer delay caller) :=
  state_rx _ (effect_arm_rx pid timer delay caller)

theorem queueSend (pid : PeerId) : StateSafe (Journal.hooks.queueSend pid) :=
  state_rx _ (modifyDev_rx _ (fun _ => rfl) (fun _ => rfl))

theorem keepalive_prepare (pid : PeerId) : StateSafe (Journal.hooks.keepalivePrepare pid) := by
  apply state_rx
  unfold RetirementSecurity.OccurrenceHandshake.keepalivePrepare
  transport_native_rx
  all_goals (split <;> transport_native_rx)
  all_goals (split <;> transport_native_rx)

theorem staging : StagingSafe (fun _ => True) origin? replay? Journal.hooks where
  keepalivePrepare := keepalive_prepare
  fixtureEnter := fun _ => state_pure _
  fixtureLeave := fun _ => state_pure _
  armTimer := armTimer
  queueSend := queueSend
  selection := selection
  reserve := reserve
  allocate := allocate
  create := create

end Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
