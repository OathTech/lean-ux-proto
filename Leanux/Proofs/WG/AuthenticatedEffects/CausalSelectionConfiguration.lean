import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionRemoval

/-! Configuration uses the actual guarded drains. Quiet native updates reuse
live-carrier frames while ordinary fixture callbacks preserve selector history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration TransmitSecurity.Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

private theorem read_write (pid : PeerId) (f : Peer → Peer) (next : Peer → WGPrefix Event α)
    (timers : ∀ p t, ((f p).internalId,(f p).timer t,(f p).wheel t) = (p.internalId,p.timer t,p.wheel t))
    (tail : ∀ p, StateSafe (next p)) :
    StateSafe (do
      let p ← effects.step (getPeer pid)
      effects.step (setPeer pid (f p))
      next p) := by
  have checked : StateSafe (do
      let p ← effects.step (getPeer pid)
      effects.step (setPeer pid (f p))
      pure p) := state_combine _
        (Delayed.state_read_write pid f pure timers (fun p => Delayed.state_pure p))
        (History.state_bind (History.state_lift _) (fun p =>
          History.state_bind (History.state_lift _) (fun _ => History.state_pure p)))
  simpa only [bind_assoc,pure_bind] using state_bind checked tail

private theorem read_modify (pid : PeerId) (f : Peer → Peer)
    (timers : ∀ p t, ((f p).internalId,(f p).timer t,(f p).wheel t) = (p.internalId,p.timer t,p.wheel t)) :
    StateSafe (do
      let p ← effects.step (getPeer pid)
      effects.step (setPeer pid (f p))) :=
  state_combine _ (Delayed.state_read_modify pid f timers)
    (History.state_bind (History.state_lift _) (fun _ => History.state_lift _))

private theorem checked_peer_write (pid : PeerId) (check : Peer → WG.M β)
    (f : Peer → Peer) (next : Peer → β → WGPrefix Event α)
    (quiet : ∀ p, SameView (fun w : WGWorld => w) (check p))
    (timers : ∀ p t, ((f p).internalId,(f p).timer t,(f p).wheel t) = (p.internalId,p.timer t,p.wheel t))
    (tail : ∀ p value, StateSafe (next p value)) :
    StateSafe (do
      let p ← liftWGPrefix (getPeer pid)
      let value ← liftWGPrefix (check p)
      liftWGPrefix (setPeer pid (f p))
      next p value) := by
  have checked : StateSafe (do
      let p ← liftWGPrefix (getPeer pid)
      let value ← liftWGPrefix (check p)
      liftWGPrefix (setPeer pid (f p))
      pure (p,value)) := state_combine _
        ((pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedConfiguration.«0».Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed.checked_peer_write)
          pid check f (fun p value => pure (p,value)) quiet timers (fun p value => Delayed.state_pure (p,value)))
        (History.state_bind (History.state_lift _) (fun p =>
          History.state_bind (History.state_lift _) (fun value =>
            History.state_bind (History.state_lift _) (fun _ => History.state_pure (p,value)))))
  simpa only [bind_assoc,pure_bind] using state_bind checked (fun pair => tail pair.1 pair.2)

open Lean Meta Elab Tactic in
elab "selection_peer_bind" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a selection state contract"
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
    have checked := hi.2.emit (event := .scope (.entered ⟨h.length,.fixture trigger⟩)) True.intro
    exact ⟨[.scope (.entered ⟨h.length,.fixture trigger⟩)],rfl,checked,hi.1.append _,checked⟩
  · intro token
    exact state_bind safe (fun value => state_bind
      (state_combine _ (Delayed.state_emit _) (Selections.state_leave token)) (fun _ => state_pure value))

macro "selection_config_step" : tactic => `(tactic| first
  | (selection_peer_bind; first
      | (apply read_modify; intro p t; rfl)
      | (apply read_write; · intro p t; rfl))
  | (selection_carrier_head liftWGPrefix; apply state_native; solve | causal_delayed_config_step)
  | selection_removal_step)

theorem configOut_safe (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateSafe (configOut attrs peer ret) := by
  unfold configOut
  repeat' selection_config_step

theorem configTailFinish_safe (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateSafe (configTailFinish hooks attrs peer pid ret) := by
  unfold configTailFinish FixtureEffects.peerFinishObserved FixtureEffects.peerFinishWith
  repeat' first
    | (selection_peer_bind
       apply checked_peer_write
       · intro p initial
         change Preserves (fun w : WGWorld => w = initial) _
         simp only [WG.andM,branch]
         repeat' first
           | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
           | rx_retention_step
       · intro p t; rfl)
    | (selection_carrier_head FixtureEffects.runWith; apply fixture)
    | (selection_carrier_head configOut; exact configOut_safe _ _ _)
    | (selection_carrier_head stagingObserved; exact staging _)
    | (selection_carrier_head keepaliveObserved; exact keepalive _)
    | selection_config_step

theorem configTail_safe (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) :
    StateSafe (configTail hooks attrs peer pid) := by
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (selection_carrier_head configOut; exact configOut_safe _ _ _)
    | (selection_carrier_head configTailFinish; exact configTailFinish_safe _ _ _ _)
    | selection_config_step

theorem configUpdate_safe
    (attrs : PeerAttrs)
    (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateSafe (configUpdate hooks attrs peer flags psk pid) := by
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (selection_carrier_head configOut; exact configOut_safe _ _ _)
    | (selection_carrier_head configTail; exact configTail_safe _ _ _)
    | (selection_carrier_head removeObserved; exact remove _)
    | selection_config_step

theorem configPeer_safe
    (attrs : PeerAttrs) :
    StateSafe (configPeer hooks attrs) := by
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (selection_carrier_head configOut; exact configOut_safe _ _ _)
    | (selection_carrier_head configUpdate; exact configUpdate_safe _ _ _ _ _)
    | selection_config_step

theorem configPeers_safe
    (attrs : DeviceAttrs) :
    StateSafe (configPeers hooks attrs) := by
  unfold configPeers devicePeersWith
  repeat' first
    | (selection_carrier_head configPeer; exact configPeer_safe _)
    | selection_config_step

theorem configKey_safe
    (attrs : DeviceAttrs) :
    StateSafe (configKey hooks attrs) := by
  unfold configKey deviceKeyWith
  repeat' first
    | (selection_carrier_head FixtureEffects.runWith; apply fixture)
    | (selection_carrier_head configPeers; exact configPeers_safe _)
    | (selection_carrier_head removeObserved; exact remove _)
    | (selection_carrier_head stagingObserved; exact staging _)
    | selection_config_step

theorem configDeviceUpdate_safe
    (attrs : DeviceAttrs) (flags : UInt32) :
    StateSafe (configDeviceUpdate hooks attrs flags) := by
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (selection_carrier_head configKey; exact configKey_safe _)
    | (selection_carrier_head removeAllObserved; exact removeAll)
    | selection_config_step

theorem configDevice_safe
    (attrs : DeviceAttrs) :
    StateSafe (configDevice hooks attrs) := by
  unfold configDevice setDeviceWith
  repeat' first
    | (selection_carrier_head configDeviceUpdate; exact configDeviceUpdate_safe _ _)
    | selection_config_step

theorem opened :
    StateSafe (openObserved hooks) := by
  unfold openObserved FixtureEffects.openObserved FixtureEffects.openWith
  repeat' first
    | (selection_carrier_head FixtureEffects.runWith; apply fixture)
    | (selection_carrier_head stagingObserved; exact staging _)
    | (selection_carrier_head keepaliveObserved; exact keepalive _)
    | selection_config_step

theorem up :
    StateSafe (upObserved hooks) := by
  unfold upObserved
  repeat' first
    | (selection_carrier_head openObserved; exact opened)
    | selection_config_step


end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
