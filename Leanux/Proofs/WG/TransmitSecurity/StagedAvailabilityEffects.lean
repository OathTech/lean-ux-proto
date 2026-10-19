import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityEffectsHistory
import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableEffects

/-! Actual timer and protocol effects preserve unconsumed staged birth credits. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000

theorem effects_frames : TimerEffects.Ops.Frames allocation? effects :=
  CausalEffects.ops_frames scope? Event.armed Event.queued allocation? (fun _ => rfl) (fun _ => rfl)

theorem modify_timer_observed (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe (TimerEffects.modifyWith effects site pid timer delay) :=
  state_history (Driver.effects_modify_history effects_history site pid timer delay)
    (TimerEffects.modify_erases (CausalEffects.ops_erases scope? Event.armed Event.queued) site pid timer delay)
    (fun _ => Native.modify_timer site pid timer delay)
    (TimerEffects.modify_frame allocation? effects_frames site pid timer delay)

theorem traversal_observed (pid : PeerId) : StateSafe (TimerEffects.traversalWith effects pid) :=
  state_history (Driver.effects_traversal_history effects_history pid)
    (TimerEffects.traversal_erases (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
    (fun _ => Native.traversal pid)
    (TimerEffects.traversal_frame allocation? effects_frames pid)

theorem data_received_observed (pid : PeerId) : StateSafe (TimerEffects.dataReceivedWith effects pid) :=
  state_history (Driver.effects_dataReceived_history effects_history pid)
    (TimerEffects.dataReceived_erases (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
    (fun _ => Native.data_received pid)
    (TimerEffects.dataReceived_frame allocation? effects_frames pid)

theorem derived_observed (pid : PeerId) : StateSafe (TimerEffects.derivedWith effects pid) := by
  apply state_history (quiet := TimerEffects.derived_frame allocation? effects_frames pid)
    (erase := TimerEffects.derived_erases
    (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
  · unfold TimerEffects.derivedWith
    simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' first
      | (driver_history_head TimerEffects.modifyWith; exact Driver.effects_modify_history effects_history _ _ _ _)
      | effect_history_step effects_history
  · intro h; exact Native.session_derived pid

theorem initiated_observed (pid : PeerId) : StateSafe (TimerEffects.initiatedWith effects pid) := by
  apply state_history (quiet := TimerEffects.initiated_frame allocation? effects_frames pid)
    (erase := TimerEffects.initiated_erases
    (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
  · unfold TimerEffects.initiatedWith
    repeat' effect_history_step effects_history
  · intro h; exact Native.initiated pid

theorem data_sent_observed (pid : PeerId) : StateSafe (TimerEffects.dataSentWith effects pid) := by
  apply state_history (quiet := TimerEffects.dataSent_frame allocation? effects_frames pid)
    (erase := TimerEffects.dataSent_erases
    (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
  · unfold TimerEffects.dataSentWith
    repeat' effect_history_step effects_history
  · intro h; exact Native.data_sent pid

theorem protocol_send_observed (pid : PeerId) (bytes : List UInt8) :
    StateSafe (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) :=
  state_quiet (ProtocolSocket.observed_appends _ _ _ _)
    (ProtocolSocket.observed_frame allocation? Event.protocolSocket (fun _ => rfl) scope? pid bytes)
    (ProtocolSocket.observed_erases _ _ _ _) (fun _ => Native.send_buffer pid bytes)

theorem cookie_send_observed (mac : HandshakeMac) (msg : List UInt8) (src : SkbSource) :
    StateSafe (CookieSocket.observed Event.cookieSocket mac msg src) :=
  state_quiet (CookieSocket.observed_appends _ _ _ _)
    (CookieSocket.observed_frame allocation? Event.cookieSocket (fun _ => rfl) mac msg src)
    (CookieSocket.observed_erases _ _ _ _) (fun _ => Native.cookie_reply msg src)


end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
