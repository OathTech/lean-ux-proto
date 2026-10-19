import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageScopes

/-! Native timer/work effects require the caller's existing lexical context.
The requirement is explicit at staging and receive entry and is discharged only
by actual enclosing source scopes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64)
    (live : frames ≠ []) : StateAt frames (effects.arm pid timer delay caller) :=
  state_current _ (fun _ => state_receipt _ (state_lift _) _ (fun _ => rfl) (fun _ _ => live))

theorem queue (pid : PeerId) (live : frames ≠ []) : StateAt frames (effects.append pid) :=
  state_current _ (fun _ => state_receipt _ (state_lift _) _ (fun _ => rfl) (fun _ _ => live))

macro "coverage_effect_step" live:ident : tactic => `(tactic| first
  | (coverage_head TimerEffects.Ops.step; exact state_lift _)
  | (coverage_head TimerEffects.Ops.arm; exact arm _ _ _ _ $live)
  | (coverage_head TimerEffects.Ops.append; exact queue _ $live)
  | coverage_state_step)

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (live : frames ≠ []) : StateAt frames (TimerEffects.modifyWith effects site pid timer delay) := by
  unfold TimerEffects.modifyWith
  repeat' coverage_effect_step live

theorem derived (pid : PeerId) (live : frames ≠ []) : StateAt frames (TimerEffects.derivedWith effects pid) := by
  unfold TimerEffects.derivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact state_bind (modify_timer _ _ _ _ live) (fun _ => state_pure _)

theorem traversal (pid : PeerId) (live : frames ≠ []) : StateAt frames (TimerEffects.traversalWith effects pid) := by
  unfold TimerEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (coverage_head TimerEffects.modifyWith; exact modify_timer _ _ _ _ live)
    | coverage_effect_step live

theorem data_sent (pid : PeerId) (live : frames ≠ []) : StateAt frames (TimerEffects.dataSentWith effects pid) := by
  unfold TimerEffects.dataSentWith
  repeat' coverage_effect_step live

theorem data_received (pid : PeerId) (live : frames ≠ []) : StateAt frames (TimerEffects.dataReceivedWith effects pid) := by
  unfold TimerEffects.dataReceivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (coverage_head TimerEffects.modifyWith; exact modify_timer _ _ _ _ live)
    | coverage_effect_step live

theorem initiated (pid : PeerId) (live : frames ≠ []) : StateAt frames (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  repeat' coverage_effect_step live

theorem queued (pid : PeerId) (retry : Bool) (live : frames ≠ []) : StateAt frames (TimerEffects.queuedWith effects pid retry) := by
  unfold TimerEffects.queuedWith
  repeat' coverage_effect_step live

theorem old_state (body : WGPrefix Journal.Event α) (live : frames ≠ []) : StateAt frames (state body) :=
  state_focus Event.old old? (fun _ => rfl) (fun _ _ => live) body

theorem old_product (body : PrefixM Journal.Event α) (live : frames ≠ []) : ProductAt frames (product body) :=
  product_focus Event.old old? (fun _ => rfl) (fun _ _ => live) body

theorem session (pid : PeerId) (live : frames ≠ []) : StateAt frames (CausalJournal.session pid) :=
  state_receipt _ (old_state _ live) _ (fun _ => rfl) (fun _ impossible => impossible.elim)

theorem no_key (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool)
    (live : frames ≠ []) : StateAt frames (PacketEffects.noKeyWith effects pid packets keypair invalid) := by
  unfold PacketEffects.noKeyWith
  repeat' first
    | (coverage_head TimerEffects.queuedWith; exact queued _ _ live)
    | coverage_effect_step live

theorem staging (pid : PeerId) (live : frames ≠ []) : StateAt frames (Driver.stagingObserved hooks pid) := by
  unfold Driver.stagingObserved
  repeat' first
    | (coverage_head PacketEffects.noKeyWith; exact no_key _ _ _ _ live)
    | (coverage_head Driver.Hooks.selection; exact old_state _ live)
    | (coverage_head Driver.Hooks.reserve; exact old_state _ live)
    | (coverage_head Driver.Hooks.allocate; exact old_state _ live)
    | (coverage_head Driver.Hooks.create; exact old_state _ live)
    | coverage_state_step

theorem keepalive (pid : PeerId) (live : frames ≠ []) : StateAt frames (Driver.keepaliveObserved hooks pid) := by
  unfold Driver.keepaliveObserved
  repeat' first
    | (coverage_head Driver.Hooks.keepalivePrepare; exact state_receipt _ (state_lift _) _
        (fun _ => rfl) (fun _ _ => live))
    | (coverage_head Driver.stagingObserved; exact staging _ live)
    | coverage_state_step

theorem transmit_front (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (live : frames ≠ []) : StateAt frames (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  repeat' first
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | (coverage_head Driver.Hooks.front; exact old_state _ live)
    | (coverage_head Driver.stagingObserved; exact staging _ live)
    | coverage_state_step

theorem protocol_send (pid : PeerId) (bytes : List UInt8) (live : frames ≠ []) :
    StateAt frames (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) := by
  unfold ProtocolSocket.observed ProtocolSocket.bufferWith
  repeat' first
    | (coverage_head CausalEffects.atCurrent; exact state_current _ (fun _ =>
        state_receipt _ (state_lift _) _ (fun _ => rfl) (fun _ _ => live)))
    | coverage_state_step

theorem cookie_send (mac : HandshakeMac) (msg : List UInt8) (src : SkbSource) :
    StateAt frames (CookieSocket.observed Event.cookieSocket mac msg src) :=
  state_focus (fun datagram => Event.cookieSocket ⟨mac,msg,src,datagram⟩) (fun _ => none)
    (fun _ => rfl) (fun _ impossible => impossible.elim) _

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
