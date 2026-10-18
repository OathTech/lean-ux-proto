import Leanux.Proofs.WG.Roaming.RemoteConfigurationTailSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration RemoteSilent
open RemoteDriver

theorem lift_frame (entry : RemoteMap) {α : Type} (action : WG.M α)
    (frame : SameView destinationAt action) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (liftWGPrefix action) :=
  native_lift_retained entry action (fun before=>of_frame before action frame)

theorem access_frame (entry : RemoteMap) {α : Type} (observed : MixedM α) (action : WG.M α)
    (erase : ErasesStatePrefix observed action) (frame : SameView destinationAt action) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (access RemoteDriver.Event.rx rxEvent observed) :=
  access_retained entry observed action erase (fun before=>of_frame before action frame)

theorem out_covered (entry : RemoteMap) (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (access RemoteDriver.Event.rx rxEvent (peerConfigOutPrefix attrs peer ret)) := by
  apply access_retained entry _ (do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
  · exact erasesStatePrefix_bind (peerPutMixed_erases peer) (fun _ =>
      erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _=>erasesStatePrefix_pure _))
  · exact fun before=>out_retained before attrs peer ret

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

macro "configuration_remote_access " entry:term : tactic => `(tactic| first
   | (configuration_access_head peerConfigOutPrefix; exact out_covered $entry _ _ _)
   | (configuration_access_head peerConfigTailPrefix
      exact access_retained $entry _ _ (peerConfigTailPrefix_erases _ _ _)
       (fun before=>tail_retained before _ _ _))
   | (configuration_access_head peerRemovePrefix
      exact access_retained $entry _ _ (peerRemovePrefix_erases _)
       (fun before=>RemoteMaintenance.remove before _))
   | (configuration_access_head peerRemoveAllPrefix
      exact access_retained $entry _ _ peerRemoveAllPrefix_erases RemoteMaintenance.removeAll)
   | (configuration_access_head peerPutMixed
      exact access_retained $entry _ _ (peerPutMixed_erases _) (fun before=>peerPut_remotes _ before))
   | (configuration_access_head peerGetMixed
      exact access_retained $entry _ _ (peerGetMixed_erases _) (fun before=>peerGet_retained before _))
   | (configuration_access_head sendStagedPacketsPrefix
      exact access_retained $entry _ _ (sendStagedPacketsPrefix_erases _)
       (fun before=>sendStagedPackets_remotes _ before))
   | (configuration_access_head modifyPeerKeysPrefix
      exact access_frame $entry _ _ (modifyPeerKeysPrefix_erases _ _)
       (modifyPeer_remotes _ _ (fun _=>rfl)))
   | (configuration_access_head removeByPeerPrefix
      exact access_frame $entry _ _ (removeByPeerPrefix_erases _) (RemoteMaintenance.removeByPeer_frame _))
   | (configuration_access_head pubkeyLookupPrefix
      exact access_frame $entry _ _ (pubkeyLookupPrefix_erases _) (lookup_frame _))
   | (configuration_access_head precomputeStaticStaticMixed
      exact access_frame $entry _ _ (precomputeStaticStaticMixed_erases _) (RemoteBirth.precompute_remotes _))
   | (configuration_access_head expireCurrentPeerKeypairsPrefix
      exact access_frame $entry _ _ (expireCurrentPeerKeypairsPrefix_erases _) (expiry_frame _))
   | (configuration_access_head clearPeerEndpointSrcPrefix
      exact access_frame $entry _ _ (clearPeerEndpointSrcPrefix_erases _) (RemoteMutation.clear_source_destinations _))
   | (configuration_access_head setPortPrefix
      exact access_frame $entry _ _ (setPortPrefix_erases _) (port_frame _)))

macro "configuration_remote_read " entry:term : tactic => `(tactic|
  (apply lift_frame $entry
   intro initial
   change Preserves (fun g=>destinationAt g=initial) _
   simp (config := {zeta:=false}) only [WG.andM,WG.orM,branch]
   repeat' first
     | (rx_retention_head getDev; exact (RemoteCompletion.store_remotes getDev_sameWGStore).wp (fun s=>s=initial))
     | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
     | rx_retention_step))

macro "configuration_remote_step " entry:term : tactic => `(tactic| first
  | configuration_remote_access $entry
  | (maintenance_lift_action_head branch; exact lift_frame $entry _ (ambient_frame (AmbientM.branch _ _)))
  | (maintenance_lift_action_head invariant; exact lift_frame $entry _ (ambient_frame (AmbientM.invariant _)))
  | (maintenance_lift_action_head getDev; exact lift_frame $entry _ (RemoteCompletion.store_remotes getDev_sameWGStore))
  | (maintenance_lift_action_head WG.andM; configuration_remote_read $entry)
  | (maintenance_lift_action_head WG.orM; configuration_remote_read $entry)
  | (maintenance_head Pure.pure
     exact StatePrefixEnsures.pure _ (fun _ _ _ pre=>pre.2) (fun _ _ _ pre=>pre))
  | (maintenance_head Bind.bind
     apply StatePrefixEnsures.bind (Q:=fun _ h g _=>RemoteDriver.NativeInv $entry h g))
  | (maintenance_head ForIn.forIn
     apply DriverTags.Flush.list_preserves (fun h g _=>RemoteDriver.NativeInv $entry h g) RemoteDriver.Safe
       (fun _ _ _ pre=>pre.2)
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

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
