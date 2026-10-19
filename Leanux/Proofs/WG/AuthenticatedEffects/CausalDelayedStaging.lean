import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedHooks
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedPackets
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedTimerCallbacks
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeepalive

/-! Source composition through actual staging and keepalive. The saved peer
write remains grouped with its native getter; only arm/queue receipts add live
delayed occurrences. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity HandshakeSecurity TimerSlots
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem ecn (packet : Packet) : StateSafe (liftWGPrefix (ipTunnelEcnEncap packet)) :=
  state_framed _ (fun initial => (ipTunnelEcnEncap_sameWGWorld packet).wp (Retained initial))
    ((ipTunnelEcnEncap_sameWGWorld packet).of_factor SendWorkCauses.queue QueuedOccurrences.queue (fun _ => rfl))

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved hooks pid) := by
  unfold Driver.stagingObserved
  repeat' first
    | (causal_delayed_head PacketEffects.noKeyWith; exact no_key _ _ _ _)
    | (causal_delayed_head Driver.Hooks.selection; exact selection _)
    | (causal_delayed_head Driver.Hooks.reserve; exact reserve _)
    | (causal_delayed_head Driver.Hooks.allocate; exact allocate _)
    | (causal_delayed_head Driver.Hooks.create; exact create _ _)
    | (causal_delayed_native_head ipTunnelEcnEncap; exact ecn _)
    | (causal_delayed_head liftWGPrefix; solve | causal_delayed_native)
    | causal_delayed_step

private theorem native_bind (body : WG.M α) (tail : α → WG.M β) :
    (liftWGPrefix (body >>= tail) : WGPrefix Event β) =
      (liftWGPrefix body >>= fun value => liftWGPrefix (tail value)) := by
  funext w a h
  change runWGPrefix (liftWGPrefix (body >>= tail)) w a h =
    runWGPrefix (liftWGPrefix body >>= fun value => liftWGPrefix (tail value)) w a h
  simp only [runWGPrefix,runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift]
  simp only [StateT.run_bind]
  cases run : (body.run w).run a with
  | error _ => rfl
  | ok value => rcases value with ⟨⟨value,v⟩,b⟩; rfl

private theorem keepalive_factor (pid : PeerId) : Driver.keepaliveObserved hooks pid = (do
    let ready ← liftWGPrefix (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid)
    if ready then Driver.stagingObserved hooks pid) := by
  unfold Driver.keepaliveObserved RetirementSecurity.OccurrenceHandshake.keepalivePrepare
  simp only [native_bind,bind_assoc]
  congr 1
  funext p
  congr 1
  funext empty
  split
  · simp only [native_bind,bind_assoc]
    congr 1
    funext allocation
    congr 1
    funext refused
    split
    · rfl
    · simp only [native_bind,bind_assoc]
      congr 1
  · rfl

private theorem keepalive_prepare (pid : PeerId) :
    StateSafe (liftWGPrefix (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid)) := by
  apply state_framed
  · intro initial
    unfold RetirementSecurity.OccurrenceHandshake.keepalivePrepare
    simp only [branch,hiddenAlloc]
    repeat' timer_data_step initial
  · change SameView SendWorkCauses.queue _
    intro initial
    change Preserves (fun w => SendWorkCauses.queue w = initial) _
    unfold RetirementSecurity.OccurrenceHandshake.keepalivePrepare
    simp only [branch,hiddenAlloc]
    repeat' queue_callback_step initial

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved hooks pid) := by
  rw [keepalive_factor]
  apply state_bind (keepalive_prepare pid)
  intro ready
  cases ready
  · exact state_pure _
  · exact staging pid

theorem handshake_worker : StateSafe (Driver.handshakeObserved hooks) :=
  handshake _ _ session keepalive

theorem timer_callback (pid : PeerId) (kind : PeerTimer) :
    StateSafe (Driver.timerObserved hooks pid kind) := by
  cases kind
  · exact retransmit pid
  · exact expired_keepalive _ keepalive pid
  · exact expired_new pid
  · exact expired_zero pid
  · exact persistent _ keepalive pid

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
