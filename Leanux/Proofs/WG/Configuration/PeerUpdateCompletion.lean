import Leanux.Proofs.WG.Configuration.PeerRemovalCompletion

/-! Acquired-peer configuration through replacement, removal, attributes and
the original allowed-IP/send tail. Removal completion precedes every cleanup. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes
set_option maxHeartbeats 1000000

def peerConfigUpdateObserved (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) : PrefixM RoutingCompletion Int := do
  if ← liftPrefix (branch .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0)) then
    peerRemoveObserved peer
    return ← peerConfigOutObserved a peer 0
  if ← liftPrefix (branch .peerSetPsk psk.isSome) then
    liftPrefix (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []})
  if ← liftPrefix (branch .peerHasEndpoint a.endpoint.isSome) then
    let some e := a.endpoint | liftPrefix (invariant "unreachable")
    if ← liftPrefix (WG.andM (branch .peerEndpointV4Len (e.len == 16)) (branch .peerEndpointV4Family (e.family == AF_INET))) then
      liftPrefix (setPeerEndpoint pid {family := e.family, addr := e.addr, port := e.port})
    else if ← liftPrefix (WG.andM (branch .peerEndpointV6Len (e.len == 28)) (branch .peerEndpointV6Family (e.family == AF_INET6))) then
      liftPrefix (setPeerEndpoint pid {family := e.family, addr := e.addr, port := e.port, scope := e.scope, flowinfo := e.flowinfo})
  if ← liftPrefix (branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)) then completedRemovePeer pid
  peerConfigTailObserved a peer pid

private theorem lift_psk (pid : PeerId) (psk : Option Key) :
    (liftPrefix (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []}) : PrefixM RoutingCompletion Unit) =
      (do let p ← liftPrefix (getPeer pid); liftPrefix (setPeer pid {p with presharedKey := psk.getD []})) := by
  funext w
  apply ExceptT.ext
  funext h
  change runPrefix (liftPrefix (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []})) w h =
    runPrefix (do let p ← liftPrefix (getPeer pid); liftPrefix (setPeer pid {p with presharedKey := psk.getD []})) w h
  simp only [runPrefix_bind, runPrefix_lift, StateT.run_bind]
  cases hr : (getPeer pid).run w <;> rfl

theorem peerConfigUpdateObserved_erases (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    ErasesPrefix (peerConfigUpdateObserved a peer flags psk pid) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateObserved peerConfigUpdateSource
  rw [lift_psk]
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact peerConfigTailObserved_erases _ _ _
    | with_reducible exact peerRemoveObserved_erases _
    | with_reducible exact peerConfigOutObserved_erases _ _ _
    | with_reducible exact completedRemovePeer_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals
    repeat' first
      | with_reducible exact peerConfigTailObserved_erases _ _ _
      | with_reducible exact peerRemoveObserved_erases _
      | with_reducible exact peerConfigOutObserved_erases _ _ _
      | with_reducible exact completedRemovePeer_erases _
      | with_reducible exact erasesPrefix_lift _
      | with_reducible exact erasesPrefix_pure _
      | with_reducible apply erasesPrefix_bind
      | with_reducible apply erasesPrefix_ite
      | (with_reducible intro x; try dsimp only)
      | (with_reducible split)

theorem peerConfigUpdateObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
      (peerConfigUpdateObserved a peer flags psk pid) (fun _ => CompletionState initial) := by
  have rem : PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
      (peerRemoveObserved peer) (fun _ => CompletionState initial) :=
    (peerRemoveObserved_spec initial peer).consequence (fun _ _ h => h.1) (fun _ _ _ h => h)
  have replace : PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
      (completedRemovePeer pid) (fun _ => CompletionTarget initial pid) :=
    (completedRemovePeer_spec initial pid).consequence (fun _ _ h => h.1) (fun _ _ _ h => h)
  have bad (message : String) : PrefixEnsures (CompletionTarget initial pid) (CompletionSafe initial)
      (liftPrefix (invariant message : M Unit)) (fun _ => CompletionTarget initial pid) := by
    apply PrefixEnsures.lift _ (fun _ _ h => h.1.1)
    intro h w x v hi hr
    cases hr
  unfold peerConfigUpdateObserved
  repeat' first
    | with_reducible exact peerConfigTailObserved_spec initial a shape peer pid
    | with_reducible exact peerConfigOutObserved_preserves initial a peer _
    | with_reducible exact rem
    | with_reducible exact replace
    | with_reducible exact bad _
    | with_reducible exact completion_lift_same initial pid _ (modifyPeer_routing pid (fun p => {p with presharedKey := psk.getD []}) (fun _ => rfl))
    | with_reducible exact completion_lift_same initial pid _ (setPeerEndpoint_routing pid _)
    | with_reducible apply completion_lift_same initial pid _ (routing_kernel _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible apply andM_sameKernel
    | with_reducible apply PrefixEnsures.bind
    | with_reducible apply PrefixEnsures.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

end Leanux.Proofs.WG.Configuration
