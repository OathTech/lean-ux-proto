import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedConfigurationFrames

/-! The final journal's pending timer and queued-work carrier traverses actual
configuration and open callbacks, including their guarded local send roots. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration TransmitSecurity.Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false
private theorem checked_peer_write (pid : PeerId) (check : Peer → WG.M β)
    (f : Peer → Peer) (next : Peer → β → WGPrefix Event α)
    (quiet : ∀ p, SameView (fun w : WGWorld => w) (check p))
    (timers : ∀ p t, ((f p).internalId,(f p).timer t,(f p).wheel t) =
      (p.internalId,p.timer t,p.wheel t))
    (tail : ∀ p value, StateSafe (next p value)) :
    StateSafe (do
      let p ← liftWGPrefix (getPeer pid)
      let value ← liftWGPrefix (check p)
      liftWGPrefix (setPeer pid (f p))
      next p value) := by
  let body : WGPrefix Event (Peer × β) := do
    let p ← liftWGPrefix (getPeer pid)
    let value ← liftWGPrefix (check p)
    liftWGPrefix (setPeer pid (f p))
    pure (p,value)
  let native : WG.M (Peer × β) := do
    let p ← getPeer pid
    let value ← check p
    setPeer pid (f p)
    pure (p,value)
  have safe : StateSafe body := by
    apply state_observed body native
    · exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
        erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
          erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure _)))
    · exact (StateAppends.lift _).bind (fun _ => (StateAppends.lift _).bind
        (fun _ => (StateAppends.lift _).bind (fun _ => StateAppends.pure _)))
    · apply DelayedEffects.native_retained
      · intro initial
        apply TimerSlots.retained_read initial pid
        intro p known
        apply preserves_bind ((quiet p).wp (TimerSlots.Retained initial))
        intro value
        apply preserves_bind (TimerSlots.retained_write initial pid (f p) (by
          intro t; rw [timers]; exact known t))
        intro _; exact preserves_pure _
      · exact (SendWorkCauses.peer_read_frame pid).bind (fun p =>
          ((quiet p).factor QueuedOccurrences.queue).bind (fun _ =>
            (SendWorkCauses.peer_write_frame pid (f p)).bind (fun _ => SameView.pure _ _)))
  simpa only [body,bind_assoc,pure_bind] using state_bind safe (fun pair => tail pair.1 pair.2)

open Lean Meta Elab Tactic in
elab "causal_delayed_peer_bind" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a delayed state contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a read continuation"
  let args := action.getAppArgs
  let read := args[args.size - 2]!.consumeMData.headBeta
  unless read.isAppOf ``liftWGPrefix do throwError "not a native source read"
  unless read.getAppArgs.back!.isAppOf ``getPeer do throwError "not a peer read"

theorem fixture (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α) (safe : StateSafe body) :
    StateSafe (FixtureEffects.runWith (fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  apply state_bind
  · intro w a h hi
    exact ⟨[.scope (.entered ⟨h.length,.fixture trigger⟩)],rfl,True.intro,hi.append _⟩
  · intro token
    exact state_bind safe (fun value => state_bind (state_emit _) (fun _ => state_pure value))

macro "causal_delayed_config_step" : tactic => `(tactic| first
  | (causal_delayed_read_write_head; first
      | (apply state_read_modify; intro p t; rfl)
      | (apply state_read_write; · intro p t; rfl))
  | (causal_delayed_native_head peerCreate; exact peer_create _ _)
  | (causal_delayed_native_head setAllowedip; exact allowedip _ _)
  | (causal_delayed_native_head removeByPeer; exact remove_allowed _)
  | (causal_delayed_native_head pubkeyLookup; exact pubkey _)
  | (causal_delayed_native_head precomputeStaticStatic; exact precompute _)
  | (causal_delayed_native_head setStaticIdentityPrivateKey
     exact configuration_native _ (setStaticIdentityPrivateKey_sameConfiguration _))
  | (causal_delayed_native_head cookiePrecomputeDeviceKeys
     exact configuration_native _ cookiePrecomputeDeviceKeys_sameConfiguration)
  | (causal_delayed_native_head expireCurrentPeerKeypairs; exact expire_keys _)
  | (causal_delayed_native_head setPort; exact port _)
  | (causal_delayed_native_head socketInit; exact socket_native _ (socketInit_sameSocket _))
  | (causal_delayed_native_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (causal_delayed_native_head lookupInterface; exact native_store _ ((lookupInterface_sameWGWorld _).factor wgStoreView))
  | (causal_delayed_native_head setPeerEndpoint; exact endpoint _ _)
  | (causal_delayed_native_head generatePublic; exact native_store _ ((generatePublic_sameWGWorld _).factor wgStoreView))
  | causal_delayed_removal_step)

theorem configOut_safe (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateSafe (configOut attrs peer ret) := by
  unfold configOut
  repeat' causal_delayed_config_step

theorem configTailFinish_safe (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateSafe (configTailFinish hooks attrs peer pid ret) := by
  unfold configTailFinish FixtureEffects.peerFinishObserved FixtureEffects.peerFinishWith
  repeat' first
    | (causal_delayed_peer_bind
       apply checked_peer_write
       · intro p initial
         change Preserves (fun w : WGWorld => w = initial) _
         simp only [WG.andM,branch]
         repeat' first
           | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
           | rx_retention_step
       · intro p t; rfl)
    | (causal_delayed_head FixtureEffects.runWith; apply fixture)
    | (causal_delayed_head configOut; exact configOut_safe _ _ _)
    | (causal_delayed_head stagingObserved; exact staging _)
    | (causal_delayed_head keepaliveObserved; exact keepalive _)
    | causal_delayed_config_step

theorem configTail_safe (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) :
    StateSafe (configTail hooks attrs peer pid) := by
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (causal_delayed_head configOut; exact configOut_safe _ _ _)
    | (causal_delayed_head configTailFinish; exact configTailFinish_safe _ _ _ _)
    | causal_delayed_config_step

theorem configUpdate_safe
    (attrs : PeerAttrs)
    (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateSafe (configUpdate hooks attrs peer flags psk pid) := by
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (causal_delayed_head configOut; exact configOut_safe _ _ _)
    | (causal_delayed_head configTail; exact configTail_safe _ _ _)
    | (causal_delayed_head removeObserved; exact remove _)
    | causal_delayed_config_step

theorem configPeer_safe
    (attrs : PeerAttrs) :
    StateSafe (configPeer hooks attrs) := by
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (causal_delayed_head configOut; exact configOut_safe _ _ _)
    | (causal_delayed_head configUpdate; exact configUpdate_safe _ _ _ _ _)
    | causal_delayed_config_step

theorem configPeers_safe
    (attrs : DeviceAttrs) :
    StateSafe (configPeers hooks attrs) := by
  unfold configPeers devicePeersWith
  repeat' first
    | (causal_delayed_head configPeer; exact configPeer_safe _)
    | causal_delayed_config_step

theorem configKey_safe
    (attrs : DeviceAttrs) :
    StateSafe (configKey hooks attrs) := by
  unfold configKey deviceKeyWith
  repeat' first
    | (causal_delayed_head FixtureEffects.runWith; apply fixture)
    | (causal_delayed_head configPeers; exact configPeers_safe _)
    | (causal_delayed_head removeObserved; exact remove _)
    | (causal_delayed_head stagingObserved; exact staging _)
    | causal_delayed_config_step

theorem configDeviceUpdate_safe
    (attrs : DeviceAttrs) (flags : UInt32) :
    StateSafe (configDeviceUpdate hooks attrs flags) := by
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (causal_delayed_head configKey; exact configKey_safe _)
    | (causal_delayed_head removeAllObserved; exact removeAll)
    | causal_delayed_config_step

theorem configDevice_safe
    (attrs : DeviceAttrs) :
    StateSafe (configDevice hooks attrs) := by
  unfold configDevice setDeviceWith
  repeat' first
    | (causal_delayed_head configDeviceUpdate; exact configDeviceUpdate_safe _ _)
    | causal_delayed_config_step

theorem opened :
    StateSafe (openObserved hooks) := by
  unfold openObserved FixtureEffects.openObserved FixtureEffects.openWith
  repeat' first
    | (causal_delayed_head FixtureEffects.runWith; apply fixture)
    | (causal_delayed_head stagingObserved; exact staging _)
    | (causal_delayed_head keepaliveObserved; exact keepalive _)
    | causal_delayed_config_step

theorem up :
    StateSafe (upObserved hooks) := by
  unfold upObserved
  repeat' first
    | (causal_delayed_head openObserved; exact opened)
    | causal_delayed_config_step


end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
