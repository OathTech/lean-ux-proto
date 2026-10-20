import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierLifecycle
import Leanux.Proofs.WG.AuthenticatedEffects.TransportOuterNative

/-! The actual dump source preserves authenticated RX cells while cursor
repayments retain their observed history, including a final peer deletion. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues NetlinkDump TransmitSecurity.Driver RetirementSecurity.NestedPeerRelease
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

macro "transport_dump_native" : tactic => `(tactic| first
  | (transport_carrier_native RxCredits.DumpReservation.walkSource; exact state_rx _ ((RxCredits.DumpReservation.walk_frame _ _ _).factor RxDisposition.nativeRxStore))
  | (transport_carrier_native deviceDumpHeaderSource; exact state_native _ (TransportPublication.store_preserves (deviceDumpHeader_sameWGStore _ _ _ _)))
  | (transport_carrier_native getNlSock; exact state_rx _ ((getNlSock_sameWGWorld _).factor RxDisposition.nativeRxStore))
  | (transport_carrier_native setNlSock; exact state_rx _ (TransportOuterNative.dump_rx _ (setNlSock_sameDump _ _)))
  | (transport_carrier_native lookupInterface; exact state_rx _ ((lookupInterface_sameWGWorld _).factor RxDisposition.nativeRxStore))
  | (transport_carrier_native coalesce; exact state_rx _ ((coalesce_sameWGWorld _).factor RxDisposition.nativeRxStore))
  | (transport_carrier_head liftWGPrefix; solve | apply state_rx; transport_effect_rx))

theorem dump_done (h : EffectsSafe extra origin replay hooks) (ctx : DumpCtx) :
    StateSafe extra origin replay (dumpDoneWith (nestedOps hooks) ctx) := by
  unfold dumpDoneWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | transport_dump_native
    | transport_carrier_state_step

theorem dump_replace (h : EffectsSafe extra origin replay hooks) (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) :
    StateSafe extra origin replay (dumpReplaceWith (nestedOps hooks) ctx nextCursor done) := by
  unfold dumpReplaceWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | transport_dump_native
    | transport_carrier_state_step

theorem dump_finish (h : EffectsSafe extra origin replay hooks) (seq : UInt32) (ctx : DumpCtx) (nextCursor : Option PeerId) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) (done : Bool) (peers : Option (Array PeerDumpAttrs)) :
    StateSafe extra origin replay (dumpFinishWith (nestedOps hooks) seq ctx nextCursor skb flags attrs done peers) := by
  unfold dumpFinishWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | (transport_carrier_head dumpReplaceWith; exact dump_replace h _ _ _)
    | transport_dump_native
    | transport_carrier_state_step

theorem dump_tail (h : EffectsSafe extra origin replay hooks) (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) :
    StateSafe extra origin replay (dumpTailWith (nestedOps hooks) d ctx skb flags attrs) := by
  unfold dumpTailWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | (transport_carrier_head dumpFinishWith; exact dump_finish h _ _ _ _ _ _ _ _)
    | transport_dump_native
    | transport_carrier_state_step

theorem dump_chunk (h : EffectsSafe extra origin replay hooks) (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    StateSafe extra origin replay (dumpChunkWith (nestedOps hooks) ctx seq skb) := by
  unfold dumpChunkWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | (transport_carrier_head dumpTailWith; exact dump_tail h _ _ _ _ _)
    | transport_dump_native
    | transport_carrier_state_step

theorem dump_socket (h : EffectsSafe extra origin replay hooks) (fd : Nat) :
    StateSafe extra origin replay (dumpSocketWith (nestedOps hooks) fd) := by
  unfold dumpSocketWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | (transport_carrier_head dumpChunkWith; exact dump_chunk h _ _ _)
    | (transport_carrier_head dumpDoneWith; exact dump_done h _)
    | transport_dump_native
    | transport_carrier_state_step

theorem dump_start (h : EffectsSafe extra origin replay hooks) (fd : Nat) (ref : DeviceRef) :
    StateSafe extra origin replay (dumpStartWith (nestedOps hooks) fd ref) := by
  unfold dumpStartWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | (transport_carrier_head dumpSocketWith; exact dump_socket h _)
    | transport_dump_native
    | transport_carrier_state_step

theorem dump_receive (h : EffectsSafe extra origin replay hooks) (fd : Nat) :
    StateSafe extra origin replay (dumpReceiveWith (nestedOps hooks) fd) := by
  unfold dumpReceiveWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | (transport_carrier_head dumpSocketWith; exact dump_socket h _)
    | transport_dump_native
    | transport_carrier_state_step

theorem dump_device (h : EffectsSafe extra origin replay hooks) (ref : DeviceRef) :
    StateSafe extra origin replay (dumpDeviceWith (nestedOps hooks) ref) := by
  unfold dumpDeviceWith
  simp only [nestedOps,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact h.peerRelease _)
    | (transport_carrier_head dumpStartWith; exact dump_start h _ _)
    | (transport_carrier_head dumpReceiveWith; exact dump_receive h _)
    | transport_dump_native
    | transport_carrier_state_step

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
