import Leanux.Proofs.WG.Configuration.PeerRemovalCompletion

/-! Acquired-peer configuration through replacement, removal, attributes and
the original allowed-IP/send tail. Removal completion precedes every cleanup. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes
set_option maxHeartbeats 1000000

def peerConfigUpdateObserved (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) : WGPrefix RoutingCompletion Int := do
  if ← liftWGPrefix (branch .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0)) then
    peerRemoveObserved peer
    return ← peerConfigOutObserved a peer 0
  if ← liftWGPrefix (branch .peerSetPsk psk.isSome) then
    liftWGPrefix (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []})
  if ← liftWGPrefix (branch .peerHasEndpoint a.endpoint.isSome) then
    let some e := a.endpoint | liftWGPrefix (invariant "unreachable")
    if ← liftWGPrefix (WG.andM (branch .peerEndpointV4Len (e.len == 16)) (branch .peerEndpointV4Family (e.family == AF_INET))) then
      liftWGPrefix (setPeerEndpoint pid {family := e.family, addr := e.addr, port := e.port})
    else if ← liftWGPrefix (WG.andM (branch .peerEndpointV6Len (e.len == 28)) (branch .peerEndpointV6Family (e.family == AF_INET6))) then
      liftWGPrefix (setPeerEndpoint pid {family := e.family, addr := e.addr, port := e.port, scope := e.scope, flowinfo := e.flowinfo})
  if ← liftWGPrefix (branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)) then completedRemovePeer pid
  peerConfigTailObserved a peer pid

private theorem lift_psk (pid : PeerId) (psk : Option Key) :
    (liftWGPrefix (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []}) : WGPrefix RoutingCompletion Unit) =
      (do let p ← liftWGPrefix (getPeer pid); liftWGPrefix (setPeer pid {p with presharedKey := psk.getD []})) := by
  funext w ambient h
  change runStatePrefix (liftWGPrefix (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []})) w ambient h =
    runStatePrefix (do let p ← liftWGPrefix (getPeer pid); liftWGPrefix (setPeer pid {p with presharedKey := psk.getD []})) w ambient h
  simp only [liftWGPrefix, runStatePrefix_bind, runStatePrefix_lift, StateT.run_bind]
  cases hr : ((getPeer pid).run w).run ambient <;> rfl

theorem peerConfigUpdateObserved_erases (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    ErasesStatePrefix (peerConfigUpdateObserved a peer flags psk pid) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateObserved peerConfigUpdateSource
  rw [lift_psk]
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact peerConfigTailObserved_erases _ _ _
    | with_reducible exact peerRemoveObserved_erases _
    | with_reducible exact peerConfigOutObserved_erases _ _ _
    | with_reducible exact completedRemovePeer_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all
  all_goals
    repeat' first
      | with_reducible exact peerConfigTailObserved_erases _ _ _
      | with_reducible exact peerRemoveObserved_erases _
      | with_reducible exact peerConfigOutObserved_erases _ _ _
      | with_reducible exact completedRemovePeer_erases _
      | exact erasesStatePrefix_lift _
      | with_reducible exact erasesStatePrefix_pure _
      | with_reducible apply erasesStatePrefix_bind
        | (with_reducible intro x; try dsimp only)
      | (with_reducible split)

theorem peerConfigUpdateObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (peerConfigUpdateObserved a peer flags psk pid) (fun _ h w _ => CompletionState initial h w) := by
  have rem : StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (peerRemoveObserved peer) (fun _ h w _ => CompletionState initial h w) :=
    (peerRemoveObserved_spec initial peer).consequence (fun _ _ _ h => h.1) (fun _ _ _ _ h => h)
  have replace : StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (completedRemovePeer pid) (fun _ h w _ => CompletionTarget initial pid h w) :=
    (completedRemovePeer_spec initial pid).consequence (fun _ _ _ h => h.1) (fun _ _ _ _ h => h)
  have bad (message : String) : StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (liftWGPrefix (invariant message : WG.M Unit)) (fun _ h w _ => CompletionTarget initial pid h w) := by
    apply StatePrefixEnsures.lift _ (fun _ _ _ h => h.1.1)
    intro h w ambient x v ambient' hi hr
    cases hr
  have hb (decision : Decision) (value : Bool) : SameView routingView (branch decision value) :=
    fun s => hoare_liftAmbient (AmbientM.branch decision value) (fun w => routingView w = s)
  unfold peerConfigUpdateObserved
  repeat' first
    | (maintenance_head peerConfigTailObserved; exact peerConfigTailObserved_spec initial a shape peer pid)
    | (maintenance_head peerConfigOutObserved; exact peerConfigOutObserved_preserves initial a peer _)
    | (maintenance_head peerRemoveObserved; exact rem)
    | (maintenance_head completedRemovePeer; exact replace)
    | (maintenance_lift_action_head invariant; exact bad _)
    | (maintenance_lift_action_head Bind.bind; exact completion_lift_same_wg initial pid _ (modifyPeer_routing pid (fun p => {p with presharedKey := psk.getD []}) (fun _ => rfl)))
    | (maintenance_lift_action_head setPeerEndpoint; exact completion_lift_same_wg initial pid _ (setPeerEndpoint_routing pid _))
    | (maintenance_lift_action_head branch; exact completion_lift_same_wg initial pid _ (hb _ _))
    | (maintenance_lift_action_head WG.andM; exact completion_lift_same_wg initial pid _ (DumpComposition.andM_sameView _ _ (hb _ _) (hb _ _)))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind)
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
  all_goals try simp_all

end Leanux.Proofs.WG.Configuration
