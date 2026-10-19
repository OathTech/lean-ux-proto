import Leanux.Proofs.WG.AuthenticatedEffects.TransportEffectsFrames

/-! RX authentication survives actual timer-arm and work-append callbacks.
Only those two effect contracts are premises; native guards and leaves are
proved over the receive-store projection at their real source call sites. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity.Driver TimerEffects
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
variable {E : Type} {extra : List E → Prop} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {hooks : Hooks E}

structure EffectsSafe (extra : List E → Prop) (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (hooks : Hooks E) : Prop where
  armTimer : ∀ pid timer delay caller, StateSafe extra origin replay (hooks.armTimer pid timer delay caller)
  queueSend : ∀ pid, StateSafe extra origin replay (hooks.queueSend pid)

macro "transport_effect_step " h:ident : tactic => `(tactic| first
  | (transport_carrier_head Hooks.armTimer; exact EffectsSafe.armTimer $h _ _ _ _)
  | (transport_carrier_head Hooks.queueSend; exact EffectsSafe.queueSend $h _)
  | (transport_carrier_head liftWGPrefix; solve | apply state_rx; transport_effect_rx)
  | transport_carrier_state_step)

theorem effects_modify (h : EffectsSafe extra origin replay hooks) (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe extra origin replay (modifyWith (effectOps hooks) site pid timer delay) := by
  unfold modifyWith
  simp only [effectOps,TimerEffects.observed]
  repeat' first
    | transport_effect_step h

theorem effects_queued (h : EffectsSafe extra origin replay hooks) (pid : PeerId) (retry : Bool) :
    StateSafe extra origin replay (queuedWith (effectOps hooks) pid retry) := by
  unfold queuedWith
  simp only [effectOps,TimerEffects.observed]
  repeat' first
    | transport_effect_step h

theorem effects_traversal (h : EffectsSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (traversalWith (effectOps hooks) pid) := by
  unfold traversalWith
  simp only [effectOps,TimerEffects.observed]
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (transport_carrier_head modifyWith; exact effects_modify h _ _ _ _)
    | transport_effect_step h

theorem effects_dataReceived (h : EffectsSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (dataReceivedWith (effectOps hooks) pid) := by
  unfold dataReceivedWith
  simp only [effectOps,TimerEffects.observed]
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (transport_carrier_head modifyWith; exact effects_modify h _ _ _ _)
    | transport_effect_step h

theorem effects_retransmit (h : EffectsSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (retransmitWith (effectOps hooks) pid) := by
  unfold retransmitWith
  simp only [effectOps,TimerEffects.observed]
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (transport_carrier_head modifyWith; exact effects_modify h _ _ _ _)
    | (transport_carrier_head queuedWith; exact effects_queued h _ _)
    | transport_effect_step h

theorem effects_expiredNew (h : EffectsSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (expiredNewWith (effectOps hooks) pid) := by
  unfold expiredNewWith
  simp only [effectOps,TimerEffects.observed]
  repeat' first
    | (transport_carrier_head queuedWith; exact effects_queued h _ _)
    | transport_effect_step h

theorem effects_freshReceive (h : EffectsSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (PacketEffects.freshReceiveWith (effectOps hooks) pid) := by
  unfold PacketEffects.freshReceiveWith
  simp only [effectOps,TimerEffects.observed]
  repeat' first
    | (transport_carrier_head queuedWith; exact effects_queued h _ _)
    | transport_effect_step h

theorem effects_noKey (h : EffectsSafe extra origin replay hooks) (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StateSafe extra origin replay (PacketEffects.noKeyWith (effectOps hooks) pid packets keypair invalid) := by
  unfold PacketEffects.noKeyWith
  simp only [effectOps,TimerEffects.observed]
  repeat' first
    | (transport_carrier_head queuedWith; exact effects_queued h _ _)
    | transport_effect_step h

theorem effects_prepare (h : EffectsSafe extra origin replay hooks) (pid : PeerId) (pkt : RxPacket) :
    StateSafe extra origin replay (PacketEffects.prepareWith (effectOps hooks) pid pkt) := by
  unfold PacketEffects.prepareWith
  simp only [effectOps,TimerEffects.observed]
  repeat' first
    | (transport_carrier_head PacketEffects.freshReceiveWith; exact effects_freshReceive h _)
    | (transport_carrier_head traversalWith; exact effects_traversal h _)
    | (transport_carrier_head dataReceivedWith; exact effects_dataReceived h _)
    | transport_effect_step h

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
