import Leanux.Proofs.WG.Roaming.RemoteConfigurationTailSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration RemoteSilent
open RemoteDriver

elab "configuration_access_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "not an observer contract"
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``access do Lean.throwError "not the configuration access"
  let .const actual _ := action.getAppArgs.back!.consumeMData.getAppFn
    | Lean.throwError "not a constant-headed source callback"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different source callback"

namespace Invariant

structure Contracts (P : List RemoteDriver.Event → WGWorld → Prop) : Prop where
  safe : ∀ h g, P h g → RemoteDriver.Safe h
  lift : ∀ {α : Type} (action : WG.M α),
    (∀ before, Ensures action (Retained before) (fun _ => Retained before)) →
    StatePrefixPreserves (fun h g _ => P h g) RemoteDriver.Safe (liftWGPrefix action)
  access : ∀ {α : Type} (observed : MixedM α) (action : WG.M α),
    ErasesStatePrefix observed action →
    (∀ before, Ensures action (Retained before) (fun _ => Retained before)) →
    StatePrefixPreserves (fun h g _ => P h g) RemoteDriver.Safe
      (RemoteConfiguration.access RemoteDriver.Event.rx rxEvent observed)
  endpoint : ∀ pid endpoint,
    StatePrefixPreserves (fun h g _ => P h g) RemoteDriver.Safe
      (RemoteDriver.endpointObserved pid endpoint)
  birth : ∀ key psk,
    StatePrefixPreserves (fun h g _ => P h g) RemoteDriver.Safe
      (RemoteDriver.birthObserved key psk)

variable {P : List RemoteDriver.Event → WGWorld → Prop}

theorem lift_frame (contracts : Contracts P) {α : Type} (action : WG.M α)
    (frame : SameView destinationAt action) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (liftWGPrefix action) :=
  contracts.lift action (fun before=>of_frame before action frame)

theorem access_frame (contracts : Contracts P) {α : Type} (observed : MixedM α) (action : WG.M α)
    (erase : ErasesStatePrefix observed action) (frame : SameView destinationAt action) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (access RemoteDriver.Event.rx rxEvent observed) :=
  contracts.access observed action erase (fun before=>of_frame before action frame)

theorem out_preserves (contracts : Contracts P) (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (access RemoteDriver.Event.rx rxEvent (peerConfigOutPrefix attrs peer ret)) := by
  apply contracts.access _ (do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
  · exact erasesStatePrefix_bind (peerPutMixed_erases peer) (fun _ =>
      erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _=>erasesStatePrefix_pure _))
  · exact fun before=>out_retained before attrs peer ret

macro "configuration_invariant_access " contracts:term : tactic => `(tactic| first
   | (configuration_access_head peerConfigOutPrefix; exact out_preserves $contracts _ _ _)
   | (configuration_access_head peerConfigTailPrefix
      exact ($contracts).access _ _ (peerConfigTailPrefix_erases _ _ _)
       (fun before=>tail_retained before _ _ _))
   | (configuration_access_head peerRemovePrefix
      exact ($contracts).access _ _ (peerRemovePrefix_erases _)
       (fun before=>RemoteMaintenance.remove before _))
   | (configuration_access_head peerRemoveAllPrefix
      exact ($contracts).access _ _ peerRemoveAllPrefix_erases RemoteMaintenance.removeAll)
   | (configuration_access_head peerPutMixed
      exact ($contracts).access _ _ (peerPutMixed_erases _) (fun before=>peerPut_remotes _ before))
   | (configuration_access_head peerGetMixed
      exact ($contracts).access _ _ (peerGetMixed_erases _) (fun before=>peerGet_retained before _))
   | (configuration_access_head sendStagedPacketsPrefix
      exact ($contracts).access _ _ (sendStagedPacketsPrefix_erases _)
       (fun before=>sendStagedPackets_remotes _ before))
   | (configuration_access_head modifyPeerKeysPrefix
      exact access_frame $contracts _ _ (modifyPeerKeysPrefix_erases _ _)
       (modifyPeer_remotes _ _ (fun _=>rfl)))
   | (configuration_access_head removeByPeerPrefix
      exact access_frame $contracts _ _ (removeByPeerPrefix_erases _) (RemoteMaintenance.removeByPeer_frame _))
   | (configuration_access_head pubkeyLookupPrefix
      exact access_frame $contracts _ _ (pubkeyLookupPrefix_erases _) (lookup_frame _))
   | (configuration_access_head precomputeStaticStaticMixed
      exact access_frame $contracts _ _ (precomputeStaticStaticMixed_erases _) (RemoteBirth.precompute_remotes _))
   | (configuration_access_head expireCurrentPeerKeypairsPrefix
      exact access_frame $contracts _ _ (expireCurrentPeerKeypairsPrefix_erases _) (expiry_frame _))
   | (configuration_access_head clearPeerEndpointSrcPrefix
      exact access_frame $contracts _ _ (clearPeerEndpointSrcPrefix_erases _) (RemoteMutation.clear_source_destinations _))
   | (configuration_access_head setPortPrefix
      exact access_frame $contracts _ _ (setPortPrefix_erases _) (port_frame _)))

macro "configuration_invariant_read " contracts:term : tactic => `(tactic|
  (apply lift_frame $contracts
   intro initial
   change Preserves (fun g=>destinationAt g=initial) _
   simp (config := {zeta:=false}) only [WG.andM,WG.orM,branch]
   repeat' first
     | (rx_retention_head getDev; exact (RemoteCompletion.store_remotes getDev_sameWGStore).wp (fun s=>s=initial))
     | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
     | rx_retention_step))

macro "configuration_invariant_step " predicate:term:max contracts:term : tactic => `(tactic| first
  | configuration_invariant_access $contracts
  | (maintenance_lift_action_head branch; exact lift_frame $contracts _ (ambient_frame (AmbientM.branch _ _)))
  | (maintenance_lift_action_head invariant; exact lift_frame $contracts _ (ambient_frame (AmbientM.invariant _)))
  | (maintenance_lift_action_head getDev; exact lift_frame $contracts _ (RemoteCompletion.store_remotes getDev_sameWGStore))
  | (maintenance_lift_action_head WG.andM; configuration_invariant_read $contracts)
  | (maintenance_lift_action_head WG.orM; configuration_invariant_read $contracts)
  | (maintenance_head Pure.pure
     exact StatePrefixEnsures.pure _ (fun h g _ pre=>($contracts).safe h g pre) (fun _ _ _ pre=>pre))
  | (maintenance_head Bind.bind
     apply StatePrefixEnsures.bind (Q:=fun _ h g _=>$predicate h g))
  | (maintenance_head ForIn.forIn
     apply DriverTags.Flush.list_preserves (fun h g _=>$predicate h g) RemoteDriver.Safe
       (fun h g _ pre=>($contracts).safe h g pre)
     intro item state
     unfold StatePrefixPreserves)
  | maintenance_intro
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_reduce
  | maintenance_reduce_match
  | maintenance_match
  | (maintenance_head ite; split)
  | (maintenance_head dite; split)
  | contradiction)

theorem update_preserves (contracts : Contracts P) (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (update RemoteDriver.Event.rx rxEvent RemoteDriver.Event.endpoint attrs peer flags psk pid) := by
  unfold update peerConfigUpdateWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head endpointObserved; exact contracts.endpoint _ _)
    | configuration_invariant_step P contracts

theorem acquired_preserves (contracts : Contracts P) (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (acquired RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint
        attrs key psk flags peer) := by
  unfold acquired peerCommandAcquiredWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head birthObserved; exact contracts.birth _ _)
    | (maintenance_head update; exact update_preserves contracts _ _ _ _ _)
    | configuration_invariant_step P contracts

theorem command_preserves (contracts : Contracts P) (attrs : PeerAttrs) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (command RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) := by
  unfold command setPeerCmdWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head acquired; exact acquired_preserves contracts _ _ _ _ _)
    | configuration_invariant_step P contracts

theorem devicePeers_preserves (contracts : Contracts P) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (devicePeers RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) := by
  unfold devicePeers devicePeersWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head command; exact command_preserves contracts _)
    | configuration_invariant_step P contracts

theorem deviceKey_preserves (contracts : Contracts P) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (deviceKey RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) := by
  unfold deviceKey deviceKeyWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head devicePeers; exact devicePeers_preserves contracts _)
    | (maintenance_lift_action_head generatePublic
       exact lift_frame contracts _ ((generatePublic_sameWGWorld _).factor destinationAt))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey
       exact lift_frame contracts _ (configuration_frame (setStaticIdentityPrivateKey_sameConfiguration _)))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys
       exact lift_frame contracts _ (configuration_frame cookiePrecomputeDeviceKeys_sameConfiguration))
    | configuration_invariant_step P contracts

theorem deviceUpdate_preserves (contracts : Contracts P) (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (deviceUpdate RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs flags) := by
  unfold deviceUpdate deviceUpdateWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head deviceKey; exact deviceKey_preserves contracts _)
    | (maintenance_lift_action_head modifyDev
       exact lift_frame contracts _ (modifyDev_remotes _ (fun _=>rfl)))
    | configuration_invariant_step P contracts

theorem setDevice_preserves (contracts : Contracts P) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>P h g) RemoteDriver.Safe
      (setDevice RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) := by
  unfold setDevice setDeviceWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head deviceUpdate; exact deviceUpdate_preserves contracts _ _)
    | (maintenance_lift_action_head lookupInterface
       exact lift_frame contracts _ ((lookupInterface_sameWGWorld _).factor destinationAt))
    | configuration_invariant_step P contracts

end Invariant
end Leanux.Proofs.WG.Roaming.RemoteConfiguration
