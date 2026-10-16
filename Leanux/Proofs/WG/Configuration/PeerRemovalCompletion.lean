import Leanux.Proofs.WG.Configuration.PeerTailCompletion
import Leanux.Proofs.WG.AllowedIps.RoutingFlushFrames

/-! Routing removal is recorded at its actual nested normal completion, before
peer hash removal, death marking, work flushing and final reference release. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps

def peerMakeDeadObserved (pid : PeerId) : WGPrefix RoutingCompletion Unit := do
  liftWGPrefix (modifyDev fun d => {d with peerList := d.peerList.filter (· != pid)})
  completedRemovePeer pid
  let d ← liftWGPrefix getDev
  _ ← liftWGPrefix (branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid)))
  liftWGPrefix (modifyDev fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)})
  liftWGPrefix (do let p ← getPeer pid; setPeer pid {p with isDead := true})

def peerRemoveObserved (peer : Option PeerId) : WGPrefix RoutingCompletion Unit := do
  if ← liftWGPrefix (branch .peerRemoveNull peer.isNone) then return
  let some pid := peer | liftWGPrefix (invariant "unreachable")
  peerMakeDeadObserved pid
  liftWGPrefix (peerRemoveAfterDead pid)

theorem peerMakeDeadObserved_erases (pid : PeerId) :
    ErasesStatePrefix (peerMakeDeadObserved pid) (peerMakeDead pid) := by
  unfold peerMakeDeadObserved peerMakeDead
  repeat' first
    | with_reducible exact completedRemovePeer_erases _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
  all_goals exact erasesStatePrefix_lift _

theorem peerRemoveObserved_erases (peer : Option PeerId) :
    ErasesStatePrefix (peerRemoveObserved peer) (peerRemove peer) := by
  unfold peerRemoveObserved peerRemove
  repeat' first
    | with_reducible exact peerMakeDeadObserved_erases _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all
  all_goals exact erasesStatePrefix_lift _

theorem peerMakeDeadObserved_spec (initial : FlatTable × FlatTable) (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (peerMakeDeadObserved pid) (fun _ h w _ => CompletionState initial h w) := by
  unfold peerMakeDeadObserved
  apply StatePrefixEnsures.bind (completion_lift_retains_wg initial _ (ProjectedRetainsRoutingCall.of_same (modifyDev_routing (fun d => {d with peerList := d.peerList.filter (· != pid)}) (fun _ => rfl))))
  intro _
  apply StatePrefixEnsures.bind (completedRemovePeer_spec initial pid)
  intro _
  apply StatePrefixEnsures.bind (completion_lift_same_wg initial pid _ (routing_kernel _ Leanux.Proofs.WG.Lifetimes.getDev_sameWGStore))
  intro d
  apply StatePrefixEnsures.bind (completion_lift_same_wg initial pid _
    (fun s => hoare_liftAmbient (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid)))
      (fun w => routingView w = s)))
  intro _
  apply StatePrefixEnsures.bind (completion_lift_same_wg initial pid _ (modifyDev_routing (fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}) (fun _ => rfl)))
  intro _
  intro w ambient h hi
  exact completion_lift_retains_wg initial _ (.of_same
    (modifyPeer_routing pid (fun p => {p with isDead := true}) (fun _ => rfl))) w ambient h hi.1


theorem peerRemoveObserved_spec (initial : FlatTable × FlatTable) (peer : Option PeerId) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (peerRemoveObserved peer) (fun _ h w _ => CompletionState initial h w) := by
  unfold peerRemoveObserved
  apply StatePrefixEnsures.bind (completion_lift_retains_wg initial _ (ProjectedRetainsRoutingCall.of_same
    (fun s => hoare_liftAmbient (AmbientM.branch .peerRemoveNull peer.isNone) (fun w => routingView w = s))))
  intro null
  split
  · exact StatePrefixEnsures.pure _ (fun _ _ _ h => h.1) (fun _ _ _ h => h)
  · cases peer with
    | none =>
      apply StatePrefixEnsures.lift _ (fun _ _ _ h => h.1)
      intro h w ambient x v ambient' hi hr
      cases hr
    | some pid =>
      apply StatePrefixEnsures.bind (peerMakeDeadObserved_spec initial pid)
      intro _
      exact completion_lift_retains_wg initial _ (peerRemoveAfterDead_routing pid)


/-- The saved list is captured after the completed clear and used unchanged by
both loops. Stale entries retain their original Stops. -/
def peerRemoveAllObserved : WGPrefix RoutingCompletion Unit := do
  completedFree
  let dead := (← liftWGPrefix getDev).peerList
  for pid in dead do
    _ ← liftWGPrefix (branch .peerRemoveAllIter1 true)
    peerMakeDeadObserved pid
  _ ← liftWGPrefix (branch .peerRemoveAllIter1 false)
  for pid in dead do
    _ ← liftWGPrefix (branch .peerRemoveAllIter2 true)
    liftWGPrefix (peerRemoveAfterDead pid)
  _ ← liftWGPrefix (branch .peerRemoveAllIter2 false)

theorem peerRemoveAllObserved_erases : ErasesStatePrefix peerRemoveAllObserved peerRemoveAll := by
  unfold peerRemoveAllObserved peerRemoveAll
  repeat' first
    | with_reducible exact completedFree_erases
    | with_reducible exact peerMakeDeadObserved_erases _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
  all_goals exact erasesStatePrefix_lift _

theorem peerRemoveAllObserved_spec (initial : FlatTable × FlatTable) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      peerRemoveAllObserved (fun _ h w _ => CompletionState initial h w) := by
  change StatePrefixPreserves (fun h w _ => CompletionState initial h w) (CompletionSafe initial) _
  have safe : ∀ h w (_ambient : Ambient), CompletionState initial h w → CompletionSafe initial h := fun _ _ _ h => h.1
  have hf := (completedFree_spec initial)
  have hm := fun pid => (peerMakeDeadObserved_spec initial pid)
  have hg := completion_lift_retains_wg initial _ (ProjectedRetainsRoutingCall.of_same (routing_kernel _ Leanux.Proofs.WG.Lifetimes.getDev_sameWGStore))
  have hb := fun dec value => completion_lift_retains_wg initial _ (ProjectedRetainsRoutingCall.of_same
    (fun s => hoare_liftAmbient (AmbientM.branch dec value) (fun w => routingView w = s)))
  unfold peerRemoveAllObserved
  repeat' first
    | with_reducible exact hf
    | with_reducible exact hm _
    | with_reducible exact hg
    | with_reducible exact hb _ _
    | with_reducible exact completion_lift_retains_wg initial _ (peerRemoveAfterDead_routing _)
    | with_reducible exact StatePrefixEnsures.pure _ safe (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => CompletionState initial h w) _ (fun _ => safe)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible intro x; try dsimp only)
  all_goals exact hb _ _

private theorem peerMakeDeadObserved_empty_spec (initial : FlatTable × FlatTable) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => CompletionEmpty initial h w) (CompletionSafe initial) (peerMakeDeadObserved pid) := by
  unfold peerMakeDeadObserved
  apply StatePrefixEnsures.bind (completion_empty_lift_wg initial _ (ProjectedRetainsRoutingCall.of_same (modifyDev_routing (fun d => {d with peerList := d.peerList.filter (· != pid)}) (fun _ => rfl))))
  intro _
  apply StatePrefixEnsures.bind (completedRemovePeer_empty_spec initial pid)
  intro _
  apply StatePrefixEnsures.bind (completion_empty_lift_wg initial _ (ProjectedRetainsRoutingCall.of_same
    (routing_kernel _ Leanux.Proofs.WG.Lifetimes.getDev_sameWGStore)))
  intro d
  apply StatePrefixEnsures.bind (completion_empty_lift_wg initial _ (ProjectedRetainsRoutingCall.of_same
    (fun s => hoare_liftAmbient (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid)))
      (fun w => routingView w = s))))
  intro _
  apply StatePrefixEnsures.bind (completion_empty_lift_wg initial _ (ProjectedRetainsRoutingCall.of_same (modifyDev_routing (fun d => {d with peerHashtable := d.peerHashtable.filter (·.2 != pid)}) (fun _ => rfl))))
  intro _
  exact completion_empty_lift_wg initial _ (.of_same
    (modifyPeer_routing pid (fun p => {p with isDead := true}) (fun _ => rfl)))

/-- A normal whole remove-all leaves the journal's flat tables empty even if
later cleanup deletes residents. No traversal totality is asserted. -/
theorem peerRemoveAllObserved_empty_spec (initial : FlatTable × FlatTable) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      peerRemoveAllObserved (fun _ h w _ => CompletionEmpty initial h w) := by
  unfold peerRemoveAllObserved
  apply StatePrefixEnsures.bind (completedFree_empty_spec initial)
  intro _
  change StatePrefixPreserves (fun h w _ => CompletionEmpty initial h w) (CompletionSafe initial) _
  have safe : ∀ h w (_ambient : Ambient), CompletionEmpty initial h w → CompletionSafe initial h := fun _ _ _ h => h.1.1
  have hm := fun pid => peerMakeDeadObserved_empty_spec initial pid
  have hg := completion_empty_lift_wg initial _ (ProjectedRetainsRoutingCall.of_same (routing_kernel _ Leanux.Proofs.WG.Lifetimes.getDev_sameWGStore))
  have hb := fun dec value => completion_empty_lift_wg initial _ (ProjectedRetainsRoutingCall.of_same
    (fun s => hoare_liftAmbient (AmbientM.branch dec value) (fun w => routingView w = s)))
  repeat' first
    | with_reducible exact hm _
    | with_reducible exact hg
    | with_reducible exact hb _ _
    | with_reducible exact completion_empty_lift_wg initial _ (peerRemoveAfterDead_routing _)
    | with_reducible exact StatePrefixEnsures.pure _ safe (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => CompletionEmpty initial h w) _ (fun _ => safe)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible intro x; try dsimp only)
  all_goals exact hb _ _

end Leanux.Proofs.WG.Configuration
