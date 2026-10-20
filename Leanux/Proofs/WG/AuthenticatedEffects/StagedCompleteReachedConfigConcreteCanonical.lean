import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigNativeFrames

/-! Canonical configuration witnesses expand the original source binds,
saved peer loop and error cleanup. The saved keepalive setter is grouped by
an equation of its literal read/decision/write sequence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver

elab "config_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a configuration shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn | Lean.throwError "not a constant head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do Lean.throwError "different source head"

elab "config_observer_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a configuration shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  unless action.consumeMData.isAppOf ``liftWGObserver do Lean.throwError "not an observer"
  let some body := action.getAppArgs.back? | Lean.throwError "missing observer body"
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a constant body"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do Lean.throwError "different observer body"

elab "config_nested_head " outer:ident inner:ident : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a configuration shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftWGObserver do Lean.throwError "not an observer"
  let some body := action.getAppArgs.back? | Lean.throwError "missing body"
  let .const outerName _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a named wrapper"
  unless outerName.toString.endsWith ("." ++ outer.getId.eraseMacroScopes.toString) do Lean.throwError "different wrapper"
  let some nested := body.getAppArgs.back? | Lean.throwError "missing nested action"
  let .const innerName _ := nested.consumeMData.headBeta.getAppFn | Lean.throwError "not a named action"
  unless innerName.toString.endsWith ("." ++ inner.getId.eraseMacroScopes.toString) do Lean.throwError "different nested action"

elab "config_plain_update_head" : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a configuration shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftWGObserver do Lean.throwError "not an observer"
  let body := action.getAppArgs.back!.consumeMData
  unless body.isAppOf ``Bind.bind do Lean.throwError "not a source bind"
  let parts := body.getAppArgs
  let head := parts[parts.size-2]!.consumeMData
  unless head.isAppOf ``liftWGPrefix do Lean.throwError "not a native read"
  unless head.getAppArgs.back!.consumeMData.isAppOf ``getPeer do Lean.throwError "not a peer read"
  let .lam _ _ tail _ := parts.back!.consumeMData | Lean.throwError "not a direct continuation"
  unless tail.consumeMData.isAppOf ``liftWGPrefix do Lean.throwError "not a native write"
  unless tail.consumeMData.getAppArgs.back!.consumeMData.isAppOf ``setPeer do Lean.throwError "not a peer write"

macro "config_shape_step" : tactic => `(tactic| first
  | (config_shape_head Pure.pure; exact .pure _)
  | (config_shape_head Bind.bind; apply Shape.bind)
  | (config_shape_head ForIn.forIn; apply listShape)
  | (config_observer_head Hooks.peerRelease; exact .child (.release _))
  | (config_observer_head removeObserved; exact .child (.remove _))
  | (config_observer_head removeAllObserved; exact .child .removeAll)
  | (config_nested_head runWith stagingObserved; exact .child (.staging _ _))
  | (config_nested_head runWith keepaliveObserved; exact .child (.keepalive _ _))
  | (config_observer_head ConfigSaved.observer; exact .saved _ _ _)
  | (config_nested_head liftWGPrefix peerCreate; exact .native (.create _ _))
  | (config_observer_head liftWGPrefix; solve | config_native_frames)
  | (config_observer_head Bind.bind; apply observerBindShape)
  | (config_observer_head Pure.pure; rw [liftWGObserver_pure]; exact .pure _)
  | (config_observer_head ForIn.forIn; rw [Lifecycle.Points.observer_list]; apply listShape)
  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

noncomputable def outShape (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Shape (liftWGObserver (configOut hooks attrs peer ret)) := by
  unfold configOut
  repeat' config_shape_step

def finishBody (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : WGPrefix Event Int := do
  let running := (← liftWGPrefix getDev).running
  if ← liftWGPrefix (branch .peerHasKeepalive attrs.keepalive.isSome) then
    let send ← ConfigSaved.observer pid running (attrs.keepalive.getD 0)
    if ← liftWGPrefix (branch .peerSendKeepalive send) then
      FixtureEffects.runWith (fixtureOps hooks) (.peerConfiguration attrs pid .keepalive) (keepaliveObserved hooks pid)
  if ← liftWGPrefix (branch .peerRunning running) then
    FixtureEffects.runWith (fixtureOps hooks) (.peerConfiguration attrs pid .staging) (stagingObserved hooks pid)
  configOut hooks attrs peer ret

theorem finish_factor (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    configTailFinish hooks attrs peer pid ret=finishBody attrs peer pid ret := by
  simp only [configTailFinish,FixtureEffects.peerFinishObserved,FixtureEffects.peerFinishWith,
    finishBody,ConfigSaved.observer,ConfigSaved.decision,bind_assoc,pure_bind]

noncomputable def finishShape (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Shape (liftWGObserver (configTailFinish hooks attrs peer pid ret)) := by
  rw [finish_factor]
  unfold finishBody
  repeat' first | (config_observer_head configOut; exact outShape _ _ _) | config_shape_step

noncomputable def tailShape (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Shape (liftWGObserver (configTail hooks attrs peer pid)) := by
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (config_observer_head configOut; exact outShape _ _ _)
    | (config_observer_head configTailFinish; exact finishShape _ _ _ _)
    | config_shape_step

noncomputable def updateShape (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Shape (liftWGObserver (configUpdate hooks attrs peer flags psk pid)) := by
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (config_plain_update_head; exact .psk pid psk)
    | (config_observer_head configOut; exact outShape _ _ _)
    | (config_observer_head configTail; exact tailShape _ _ _)
    | config_shape_step

noncomputable def peerShape (attrs : PeerAttrs) : Shape (liftWGObserver (configPeer hooks attrs)) := by
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (config_observer_head configOut; exact outShape _ _ _)
    | (config_observer_head configUpdate; exact updateShape _ _ _ _ _)
    | config_shape_step

noncomputable def peersShape (attrs : DeviceAttrs) : Shape (liftWGObserver (configPeers hooks attrs)) := by
  unfold configPeers devicePeersWith
  repeat' first | (config_observer_head configPeer; exact peerShape _) | config_shape_step

noncomputable def keyShape (attrs : DeviceAttrs) : Shape (liftWGObserver (configKey hooks attrs)) := by
  unfold configKey deviceKeyWith
  repeat' first | (config_observer_head configPeers; exact peersShape _) | config_shape_step

noncomputable def deviceUpdateShape (attrs : DeviceAttrs) (flags : UInt32) :
    Shape (liftWGObserver (configDeviceUpdate hooks attrs flags)) := by
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first | (config_observer_head configKey; exact keyShape _) | config_shape_step

noncomputable def deviceShape (attrs : DeviceAttrs) : Shape (liftWGObserver (configDevice hooks attrs)) := by
  unfold configDevice setDeviceWith
  repeat' first | (config_observer_head configDeviceUpdate; exact deviceUpdateShape _ _) | config_shape_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
