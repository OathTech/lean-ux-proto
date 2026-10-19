import Leanux.Proofs.WG.TransmitSecurity.StagedNativeSupportFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeContracts

/-! Additional native timer frames and observation adapters for staged origins. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000

theorem derived_observed (pid : PeerId) : StateSafe (TimerEffects.derivedWith effects pid) := by
  apply state_history (erase := TimerEffects.derived_erases
    (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
  · unfold TimerEffects.derivedWith
    simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' first
      | (driver_history_head TimerEffects.modifyWith; exact Driver.effects_modify_history effects_history _ _ _ _)
      | effect_history_step effects_history
  · intro h; exact Native.session_derived pid

theorem initiated_observed (pid : PeerId) : StateSafe (TimerEffects.initiatedWith effects pid) := by
  apply state_history (erase := TimerEffects.initiated_erases
    (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
  · unfold TimerEffects.initiatedWith
    repeat' effect_history_step effects_history
  · intro h; exact Native.initiated pid

theorem data_sent_observed (pid : PeerId) : StateSafe (TimerEffects.dataSentWith effects pid) := by
  apply state_history (erase := TimerEffects.dataSent_erases
    (CausalEffects.ops_erases scope? Event.armed Event.queued) pid)
  · unfold TimerEffects.dataSentWith
    repeat' effect_history_step effects_history
  · intro h; exact Native.data_sent pid

theorem state_scope (cause : Cause) (body : WGPrefix Event α) (safe : StateSafe body) :
    StateSafe (CausalScope.scope Event.scope cause body) :=
  CausalScope.scope_preserves Event.scope cause body (fun _ _ _ before => before.2)
    (fun event h _ _ before => ⟨before.1.append _,before.2.emit (checked_quiet (.scope event) True.intro h)⟩) safe

theorem state_bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (safe : StateSafe body) (tail : ∀ value, StateSafe (next value)) : StateSafe (body >>= next) :=
  StatePrefixEnsures.bind safe tail

theorem state_ite (p : Prop) [Decidable p] {left right : WGPrefix Event α}
    (hl : p → StateSafe left) (hr : ¬ p → StateSafe right) : StateSafe (if p then left else right) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hl hp
  · exact hr hp

theorem state_forIn {α β : Type} (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (safe : ∀ value acc, StateSafe (body value acc)) : StateSafe (forIn xs initial body) :=
  StatePrefixEnsures.forInInvariant xs initial body (fun _ h w _ => Carrier h w) Safe
    (fun _ _ _ _ before => before.2) safe

theorem protocol_send_observed (pid : PeerId) (bytes : List UInt8) :
    StateSafe (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) :=
  state_quiet (ProtocolSocket.observed_appends _ _ _ _)
    (ProtocolSocket.observed_frame selection? Event.protocolSocket (fun _ => rfl) scope? pid bytes)
    (ProtocolSocket.observed_erases _ _ _ _) (fun _ => Native.send_buffer pid bytes)

theorem cookie_send_observed (mac : HandshakeMac) (msg : List UInt8) (src : SkbSource) :
    StateSafe (CookieSocket.observed Event.cookieSocket mac msg src) :=
  state_quiet (CookieSocket.observed_appends _ _ _ _)
    (CookieSocket.observed_frame selection? Event.cookieSocket (fun _ => rfl) mac msg src)
    (CookieSocket.observed_erases _ _ _ _) (fun _ => Native.cookie_reply msg src)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
