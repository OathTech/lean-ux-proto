import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionStaging
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDisposal

/-! All five original timer callbacks preserve live socket occurrence
accounting; their native arms and work queues retain separate causal receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem endpoint_src (pid : PeerId) : StateSafe (effects.step (clearPeerEndpointSrc pid)) := by
  apply state_native
  sent_frame [clearPeerEndpointSrc,dstCacheResetNow,dstCacheReset,getAmbient,hiddenJiffies]
    using [getPeer_sent_spec,setPeer_sent_spec]

private theorem purge (pid : PeerId) : StateSafe (effects.step (purgeStagedPackets pid)) := by
  apply state_native
  sent_frame [purgeStagedPackets] using [getPeer_sent_spec,setPeer_sent_spec]

theorem expired_zero (pid : PeerId) : StateSafe (effects.step (expiredZeroKeyMaterial pid)) := by
  apply state_native
  sent_frame [expiredZeroKeyMaterial,peekQueuedUnit,recordQueued]
    using [getPeer_sent_spec,setPeer_sent_spec,peerGet_sent_spec,peerPut_sent_spec]

theorem retransmit (pid : PeerId) : StateSafe (TimerEffects.retransmitWith effects pid) := by
  unfold TimerEffects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_head TimerEffects.Ops.step; change StateSafe (liftWGPrefix _))
    | (emission_native_head delTimer; exact state_native _ (EmissionFrames.delete _ _))
    | (emission_native_head purgeStagedPackets; exact purge _)
    | (emission_native_head clearPeerEndpointSrc; exact endpoint_src _)
    | (emission_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | (emission_head TimerEffects.queuedWith; exact queued _ _)
    | emission_effect_step

theorem queued_release (pid : PeerId) (retry : Bool) :
    StateSafe (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects hooks.peerRelease pid retry) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.queuedWith
  repeat' first
    | (emission_head Driver.Hooks.peerRelease; exact peer_release _)
    | (emission_head TimerEffects.Ops.step; change StateSafe (liftWGPrefix _))
    | emission_effect_step

theorem retransmit_observed (pid : PeerId) : StateSafe
    (HandshakeSecurity.StagedDisposal.Effects.retransmitWith effects hooks.peerRelease hooks.stagedPurge pid) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.retransmitWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_head Driver.Hooks.stagedPurge; exact staged_purge _)
    | (emission_head TimerEffects.Ops.step; change StateSafe (liftWGPrefix _))
    | (emission_native_head delTimer; exact state_native _ (EmissionFrames.delete _ _))
    | (emission_native_head clearPeerEndpointSrc; exact endpoint_src _)
    | (emission_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | (emission_head HandshakeSecurity.StagedDisposal.Effects.queuedWith; exact queued_release _ _)
    | emission_effect_step

theorem expired_new_observed (pid : PeerId) : StateSafe
    (HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith effects hooks.peerRelease pid) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith
  exact state_bind (endpoint_src pid) (fun _ => queued_release pid false)

theorem expired_keepalive (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) :
    StateSafe (TimerEffects.expiredKeepaliveWith effects keepalive pid) := by
  unfold TimerEffects.expiredKeepaliveWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_head TimerEffects.Ops.step; change StateSafe (liftWGPrefix _))
    | exact hk _
    | (emission_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | emission_effect_step

theorem expired_new (pid : PeerId) : StateSafe (TimerEffects.expiredNewWith effects pid) := by
  unfold TimerEffects.expiredNewWith
  repeat' first
    | (emission_head TimerEffects.Ops.step; change StateSafe (liftWGPrefix _))
    | (emission_native_head clearPeerEndpointSrc; exact endpoint_src _)
    | (emission_head TimerEffects.queuedWith; exact queued _ _)
    | emission_effect_step

theorem persistent (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) :
    StateSafe (TimerEffects.persistentWith effects keepalive pid) := by
  unfold TimerEffects.persistentWith
  repeat' first
    | (emission_head TimerEffects.Ops.step; change StateSafe (liftWGPrefix _))
    | exact hk _
    | emission_effect_step

theorem timer (keepalive : PeerId → WGPrefix Event Unit)
    (hk : ∀ pid, StateSafe (keepalive pid)) (pid : PeerId) (kind : PeerTimer) :
    StateSafe (TimerEffects.timerWith effects keepalive pid kind) := by
  cases kind
  · exact retransmit pid
  · exact expired_keepalive keepalive hk pid
  · exact expired_new pid
  · exact expired_zero pid
  · exact persistent keepalive hk pid

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
