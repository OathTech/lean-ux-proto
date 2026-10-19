import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsSource
import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootFrames

/-! Native erasure of the callback-parametric timer and queue source. This is
separate from journal projection: both native results and native Stops agree. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

structure Ops.Erases (g : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (a : WG.M α), ErasesStatePrefix (g.step a) a
  arm : ∀ pid timer delay caller, ErasesStatePrefix
    (g.arm pid timer delay caller) (armTimer pid timer delay caller)
  append : ∀ pid, ErasesStatePrefix (g.append pid)
    (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})

macro "timer_effects_erase " h:ident : tactic => `(tactic| first
  | exact Ops.Erases.step $h _
  | exact Ops.Erases.arm $h _ _ _ _
  | exact Ops.Erases.append $h _
  | work_root_erasure_step)

variable {g : Ops (WGPrefix E)}

theorem modify_erases (h : Ops.Erases g) (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    ErasesStatePrefix (modifyWith g site pid timer delay) (modPeerTimer site pid timer delay) := by
  unfold modifyWith modPeerTimer
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | timer_effects_erase h

theorem derived_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (derivedWith g pid) (timersSessionDerived pid) := by
  unfold derivedWith timersSessionDerived
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_erases h _ _ _ _
    | timer_effects_erase h

theorem traversal_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (traversalWith g pid) (timersTraversal pid) := by
  unfold traversalWith timersTraversal
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_erases h _ _ _ _
    | timer_effects_erase h

theorem dataSent_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (dataSentWith g pid) (timersDataSent pid) := by
  unfold dataSentWith timersDataSent
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | timer_effects_erase h

theorem dataReceived_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (dataReceivedWith g pid) (timersDataReceived pid) := by
  unfold dataReceivedWith timersDataReceived
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_erases h _ _ _ _
    | timer_effects_erase h

theorem initiated_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (initiatedWith g pid) (timersHandshakeInitiated pid) := by
  unfold initiatedWith timersHandshakeInitiated
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | timer_effects_erase h

theorem queued_erases (h : Ops.Erases g) (pid : PeerId) (retry : Bool) :
    ErasesStatePrefix (queuedWith g pid retry) (sendQueuedHandshakeInitiation pid retry) := by
  unfold queuedWith sendQueuedHandshakeInitiation
  repeat' first
    | timer_effects_erase h

theorem retransmit_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (retransmitWith g pid) (expiredRetransmitHandshake pid) := by
  unfold retransmitWith expiredRetransmitHandshake
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_erases h _ _ _ _
    | with_reducible exact queued_erases h _ _
    | timer_effects_erase h

theorem expiredNew_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (expiredNewWith g pid) (expiredNewHandshake pid) := by
  unfold expiredNewWith expiredNewHandshake
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact queued_erases h _ _
    | timer_effects_erase h

theorem expiredKeepalive_erases (h : Ops.Erases g)
    (keepalive : PeerId → WGPrefix E Unit)
    (hk : ∀ pid, ErasesStatePrefix (keepalive pid) (sendKeepalive pid)) (pid : PeerId) :
    ErasesStatePrefix (expiredKeepaliveWith g keepalive pid) (expiredSendKeepalive pid) := by
  unfold expiredKeepaliveWith expiredSendKeepalive
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | exact hk _
    | with_reducible exact modify_erases h _ _ _ _
    | timer_effects_erase h

theorem persistent_erases (h : Ops.Erases g)
    (keepalive : PeerId → WGPrefix E Unit)
    (hk : ∀ pid, ErasesStatePrefix (keepalive pid) (sendKeepalive pid)) (pid : PeerId) :
    ErasesStatePrefix (persistentWith g keepalive pid) (expiredSendPersistentKeepalive pid) := by
  unfold persistentWith expiredSendPersistentKeepalive
  repeat' first | exact hk _ | timer_effects_erase h

theorem timer_erases (h : Ops.Erases g)
    (keepalive : PeerId → WGPrefix E Unit)
    (hk : ∀ pid, ErasesStatePrefix (keepalive pid) (sendKeepalive pid)) (pid : PeerId) (timer : PeerTimer) :
    ErasesStatePrefix (timerWith g keepalive pid timer) (timerCallback pid timer) := by
  cases timer
  · exact retransmit_erases h pid
  · exact expiredKeepalive_erases h keepalive hk pid
  · exact expiredNew_erases h pid
  · exact h.step _
  · exact persistent_erases h keepalive hk pid

end Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
