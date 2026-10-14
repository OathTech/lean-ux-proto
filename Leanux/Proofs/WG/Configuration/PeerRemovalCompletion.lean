import Leanux.Proofs.WG.Configuration.PeerTailCompletion
import Leanux.Proofs.WG.AllowedIps.RoutingFlushFrames

/-! Routing removal is recorded at its actual nested normal completion, before
peer hash removal, death marking, work flushing and final reference release. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps

def peerMakeDeadObserved (pid : PeerId) : PrefixM RoutingCompletion Unit := do
  liftPrefix (modifyDev fun d => {d with peerList := d.peerList.filter (· != pid)})
  completedRemovePeer pid
  liftPrefix (modifyDev fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)})
  liftPrefix (do let p ← getPeer pid; setPeer pid {p with isDead := true})

def peerRemoveObserved (peer : Option PeerId) : PrefixM RoutingCompletion Unit := do
  if ← liftPrefix (branch .peerRemoveNull peer.isNone) then return
  let some pid := peer | liftPrefix (invariant "unreachable")
  peerMakeDeadObserved pid
  liftPrefix (peerRemoveAfterDead pid)

theorem peerMakeDeadObserved_erases (pid : PeerId) :
    ErasesPrefix (peerMakeDeadObserved pid) (peerMakeDead pid) := by
  unfold peerMakeDeadObserved peerMakeDead
  simp only [bind_assoc]
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
    erasesPrefix_bind (completedRemovePeer_erases _) (fun _ =>
    erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _)))

theorem peerRemoveObserved_erases (peer : Option PeerId) :
    ErasesPrefix (peerRemoveObserved peer) (peerRemove peer) := by
  unfold peerRemoveObserved peerRemove
  repeat' first
    | with_reducible exact peerMakeDeadObserved_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem peerMakeDeadObserved_spec (initial : FlatTable × FlatTable) (pid : PeerId) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (peerMakeDeadObserved pid) (fun _ => CompletionState initial) := by
  unfold peerMakeDeadObserved
  apply PrefixEnsures.bind (completion_lift_retains initial _ (.of_same (modifyDev_routing (fun d => {d with peerList := d.peerList.filter (· != pid)}) (fun _ => rfl))))
  intro _
  apply PrefixEnsures.bind (completedRemovePeer_spec initial pid)
  intro _
  apply PrefixEnsures.bind (completion_lift_same initial pid _ (modifyDev_routing (fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}) (fun _ => rfl)))
  intro _
  intro w h hi
  exact completion_lift_retains initial _ (.of_same
    (modifyPeer_routing pid (fun p => {p with isDead := true}) (fun _ => rfl))) w h hi.1


theorem peerRemoveObserved_spec (initial : FlatTable × FlatTable) (peer : Option PeerId) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (peerRemoveObserved peer) (fun _ => CompletionState initial) := by
  unfold peerRemoveObserved
  apply PrefixEnsures.bind (completion_lift_retains initial _ (.of_same (routing_kernel _ (sameKernel_branch _ _))))
  intro null
  split
  · exact PrefixEnsures.pure (fun _ _ h => h.1) (fun _ _ h => h)
  · cases peer with
    | none =>
      apply PrefixEnsures.lift _ (fun _ _ h => h.1)
      intro h w x v hi hr
      cases hr
    | some pid =>
      apply PrefixEnsures.bind (peerMakeDeadObserved_spec initial pid)
      intro _
      exact completion_lift_retains initial _ (peerRemoveAfterDead_routing pid)

end Leanux.Proofs.WG.Configuration
