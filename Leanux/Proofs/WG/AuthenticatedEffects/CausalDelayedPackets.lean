import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedEffects

/-! Packet-side key refresh and receive maintenance preserve the final
journal's live timer/work occurrences. Native retirement, statistics and
header updates do not create a delayed-effect origin. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TimerSlots Queues.WorkQueueFrames
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem fresh_send (pid : PeerId) : StateSafe (PacketEffects.freshSendWith effects pid) := by
  unfold PacketEffects.freshSendWith
  repeat' first
    | (causal_delayed_head TimerEffects.queuedWith; exact queued _ _)
    | causal_delayed_effect_step

theorem fresh_receive (pid : PeerId) : StateSafe (PacketEffects.freshReceiveWith effects pid) := by
  unfold PacketEffects.freshReceiveWith
  repeat' first
    | (causal_delayed_head TimerEffects.queuedWith; exact queued _ _)
    | causal_delayed_effect_step

theorem no_key (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StateSafe (PacketEffects.noKeyWith effects pid packets keypair invalid) := by
  unfold PacketEffects.noKeyWith
  repeat' first
    | (causal_delayed_head TimerEffects.queuedWith; exact queued _ _)
    | causal_delayed_effect_step

private theorem stats (pid : PeerId) (len : Nat) : StateSafe (effects.step (updateRxStats pid len)) := by
  apply state_framed
  · intro initial
    unfold updateRxStats
    repeat' causal_delayed_timer_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    unfold updateRxStats
    repeat' causal_delayed_queue_step initial

private theorem dishonest_frame (why : Dishonest) : StateSafe (effects.step (dishonest why)) := by
  cases why <;> unfold dishonest <;> causal_delayed_native

private theorem ecn (protocol outer : Nat) (bytes : List UInt8) :
    StateSafe (effects.step (inetEcnDecapsulate protocol outer bytes)) :=
  state_framed _ (retained_store (inetEcnDecapsulate_sameWGStore protocol outer bytes))
    (DelayedEffects.queue_of_frame (store (inetEcnDecapsulate_sameWGStore protocol outer bytes)))

theorem prepare (pid : PeerId) (packet : RxPacket) :
    StateSafe (PacketEffects.prepareWith effects pid packet) := by
  unfold PacketEffects.prepareWith
  repeat' first
    | (causal_delayed_head PacketEffects.freshReceiveWith; exact fresh_receive _)
    | (causal_delayed_native_head timersAnyAuthenticatedPacketReceived; exact delete _ _)
    | (causal_delayed_head TimerEffects.traversalWith; exact traversal _)
    | (causal_delayed_head TimerEffects.dataReceivedWith; exact data_received _)
    | (causal_delayed_native_head updateRxStats; exact stats _ _)
    | (causal_delayed_native_head dishonest; exact dishonest_frame _)
    | (causal_delayed_native_head inetEcnDecapsulate; exact ecn _ _ _)
    | causal_delayed_effect_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
