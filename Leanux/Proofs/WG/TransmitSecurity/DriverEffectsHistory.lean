import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase

/-! History-only contracts for timer and packet effects, separate from native
state frames and from the causal invariant that will authorize each effect. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects TimerEffects
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure EffectsHistory (Safe : List E → Prop) (ops : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (action : WG.M α), StateHistorySafe Safe (ops.step action)
  arm : ∀ pid timer delay caller, StateHistorySafe Safe (ops.arm pid timer delay caller)
  append : ∀ pid, StateHistorySafe Safe (ops.append pid)

macro "effect_history_step " h:ident : tactic => `(tactic| first
  | (driver_history_head Ops.step; exact EffectsHistory.step $h _)
  | (driver_history_head Ops.arm; exact EffectsHistory.arm $h _ _ _ _)
  | (driver_history_head Ops.append; exact EffectsHistory.append $h _)
  | driver_state_history_step)

variable {Safe : List E → Prop} {ops : Ops (WGPrefix E)}

theorem effects_modify_history (h : EffectsHistory Safe ops) (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateHistorySafe Safe (modifyWith ops site pid timer delay) := by
  unfold modifyWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | effect_history_step h

theorem effects_queued_history (h : EffectsHistory Safe ops) (pid : PeerId) (retry : Bool) :
    StateHistorySafe Safe (queuedWith ops pid retry) := by
  unfold queuedWith
  repeat' first
    | effect_history_step h

theorem effects_traversal_history (h : EffectsHistory Safe ops) (pid : PeerId) :
    StateHistorySafe Safe (traversalWith ops pid) := by
  unfold traversalWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head modifyWith; exact effects_modify_history h _ _ _ _)
    | effect_history_step h

theorem effects_dataReceived_history (h : EffectsHistory Safe ops) (pid : PeerId) :
    StateHistorySafe Safe (dataReceivedWith ops pid) := by
  unfold dataReceivedWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head modifyWith; exact effects_modify_history h _ _ _ _)
    | effect_history_step h

theorem effects_retransmit_history (h : EffectsHistory Safe ops) (pid : PeerId) :
    StateHistorySafe Safe (retransmitWith ops pid) := by
  unfold retransmitWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head modifyWith; exact effects_modify_history h _ _ _ _)
    | (driver_history_head queuedWith; exact effects_queued_history h _ _)
    | effect_history_step h

theorem effects_expiredNew_history (h : EffectsHistory Safe ops) (pid : PeerId) :
    StateHistorySafe Safe (expiredNewWith ops pid) := by
  unfold expiredNewWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head queuedWith; exact effects_queued_history h _ _)
    | effect_history_step h

theorem effects_freshReceive_history (h : EffectsHistory Safe ops) (pid : PeerId) :
    StateHistorySafe Safe (PacketEffects.freshReceiveWith ops pid) := by
  unfold PacketEffects.freshReceiveWith
  repeat' first
    | (driver_history_head queuedWith; exact effects_queued_history h _ _)
    | effect_history_step h

theorem effects_noKey_history (h : EffectsHistory Safe ops) (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StateHistorySafe Safe (PacketEffects.noKeyWith ops pid packets keypair invalid) := by
  unfold PacketEffects.noKeyWith
  repeat' first
    | (driver_history_head queuedWith; exact effects_queued_history h _ _)
    | effect_history_step h

theorem effects_prepare_history (h : EffectsHistory Safe ops) (pid : PeerId) (pkt : RxPacket) :
    StateHistorySafe Safe (PacketEffects.prepareWith ops pid pkt) := by
  unfold PacketEffects.prepareWith
  repeat' first
    | (driver_history_head PacketEffects.freshReceiveWith; exact effects_freshReceive_history h _)
    | (driver_history_head traversalWith; exact effects_traversal_history h _)
    | (driver_history_head dataReceivedWith; exact effects_dataReceived_history h _)
    | effect_history_step h

theorem effects_expiredKeepalive_history (h : EffectsHistory Safe ops)
    (keepalive : PeerId → WGPrefix E Unit) (hk : ∀ pid, StateHistorySafe Safe (keepalive pid))
    (pid : PeerId) : StateHistorySafe Safe (expiredKeepaliveWith ops keepalive pid) := by
  unfold expiredKeepaliveWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | exact hk _
    | (driver_history_head modifyWith; exact effects_modify_history h _ _ _ _)
    | effect_history_step h

theorem effects_persistent_history (h : EffectsHistory Safe ops)
    (keepalive : PeerId → WGPrefix E Unit) (hk : ∀ pid, StateHistorySafe Safe (keepalive pid))
    (pid : PeerId) : StateHistorySafe Safe (persistentWith ops keepalive pid) := by
  unfold persistentWith
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | exact hk _
    | (driver_history_head modifyWith; exact effects_modify_history h _ _ _ _)
    | effect_history_step h

theorem HooksHistorySafe.effects {hooks : Hooks E} (h : HooksHistorySafe Safe hooks) :
    EffectsHistory Safe (effectOps hooks) where
  step := History.state_lift
  arm := h.armTimer
  append := h.queueSend

theorem ActorHistorySafe.effects {hooks : Hooks E} (h : ActorHistorySafe Safe hooks) :
    EffectsHistory Safe (effectOps hooks) where
  step := History.state_lift
  arm := h.armTimer
  append := h.queueSend

end Leanux.Proofs.WG.TransmitSecurity.Driver
