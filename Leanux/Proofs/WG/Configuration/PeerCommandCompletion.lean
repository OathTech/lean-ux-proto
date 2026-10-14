import Leanux.Proofs.WG.Configuration.PeerUpdateCompletion
import Leanux.Proofs.WG.AllowedIps.RoutingAcquire

/-! Literal public peer configuration with completed routing cuts retained on
later Stop. Public-key lookup establishes raw-slot residency, not affiliation. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

private def peerCommandAcquiredObserved (a : PeerAttrs) (publicKey : Key)
    (psk : Option Key) (flags : UInt32) (peer : Option PeerId) : PrefixM RoutingCompletion Int := do
  let mut flags := flags
  let mut peer := peer
  if ← liftPrefix (branch .peerNotFound peer.isNone) then
    if ← liftPrefix (branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0)) then
      return ← peerConfigOutObserved a none 0
    flags := flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS
    let id := (← liftPrefix getDev).staticIdentity
    if ← liftPrefix (WG.andM (branch .peerSelfHasIdentity id.hasIdentity) (branch .peerSelfKeyMatch (publicKey == id.staticPublic))) then
      return ← peerConfigOutObserved a none 0
    match ← liftPrefix (peerCreate publicKey psk) with
    | .error e =>
      _ ← liftPrefix (branch .peerCreateErr true)
      return ← peerConfigOutObserved a none e
    | .ok pid =>
      _ ← liftPrefix (branch .peerCreateErr false)
      liftPrefix (peerGet pid)
      peer := some pid
  let some pid := peer | liftPrefix (invariant "set_peer without a peer")
  peerConfigUpdateObserved a peer flags psk pid

def setPeerCmdObserved (a : PeerAttrs) : PrefixM RoutingCompletion Int := do
  if !(← liftPrefix (WG.andM (branch .peerHasPubkey a.publicKey.isSome) (branch .peerPubkeyLen true))) then
    return ← peerConfigOutObserved a none (-EINVAL)
  let some publicKey := a.publicKey | liftPrefix (invariant "unreachable")
  let psk ← do
    if ← liftPrefix (WG.andM (branch .peerHasPsk a.presharedKey.isSome) (branch .peerPskLen true)) then pure a.presharedKey
    else pure none
  let mut flags : UInt32 := 0
  if ← liftPrefix (branch .peerHasFlags a.flags.isSome) then flags := a.flags.getD 0
  if ← liftPrefix (branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0)) then return ← peerConfigOutObserved a none (-EOPNOTSUPP)
  if ← liftPrefix (branch .peerHasProtocol a.protocolVersion.isSome) then
    if ← liftPrefix (branch .peerBadProtocol (a.protocolVersion != some 1)) then return ← peerConfigOutObserved a none (-EPFNOSUPPORT)
  let mut peer ← liftPrefix (pubkeyLookup publicKey)
  peerCommandAcquiredObserved a publicKey psk flags peer

theorem setPeerCmdObserved_erases (a : PeerAttrs) :
    ErasesPrefix (setPeerCmdObserved a) (setPeerCmd a) := by
  rw [← setPeerCmd_source]
  unfold setPeerCmdObserved peerCommandAcquiredObserved setPeerCmdSource
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact peerConfigUpdateObserved_erases _ _ _ _ _
    | with_reducible exact peerConfigOutObserved_erases _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals try simp only [map_eq_pure_bind]
  all_goals
    repeat' first
      | with_reducible exact peerConfigUpdateObserved_erases _ _ _ _ _
      | with_reducible exact peerConfigOutObserved_erases _ _ _
      | with_reducible exact erasesPrefix_lift _
      | with_reducible exact erasesPrefix_pure _
      | with_reducible apply erasesPrefix_bind
      | with_reducible apply erasesPrefix_ite
      | (with_reducible intro x; try dsimp only)
      | (with_reducible split)

private theorem completion_same (initial : FlatTable × FlatTable)
    (P : List RoutingCompletion → World → Prop)
    (safe : ∀ h w, P h w → CompletionSafe initial h)
    (frame : ∀ h w v, routingView v = routingView w → P h w → P h v)
    (a : M α) (ha : SameView routingView a) :
    PrefixEnsures P (CompletionSafe initial) (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a safe
  intro h w x v hi hr
  exact frame h w v (ha w x v hr) hi

private theorem completion_state_same (initial : FlatTable × FlatTable)
    (a : M α) (ha : SameView routingView a) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (liftPrefix a) (fun _ => CompletionState initial) :=
  completion_same initial _ (fun _ _ hi => hi.1)
    (fun _ _ _ he hi => ⟨hi.1, he ▸ hi.2⟩) a ha

private theorem completion_acquired_same (initial : FlatTable × FlatTable) (peer : Option PeerId)
    (a : M α) (ha : SameView routingView a) :
    PrefixEnsures (CompletionAcquired initial peer) (CompletionSafe initial)
      (liftPrefix a) (fun _ => CompletionAcquired initial peer) :=
  completion_same initial _ (fun _ _ hi => hi.1.1)
    (fun _ _ _ he hi => ⟨⟨hi.1.1, he ▸ hi.1.2⟩, fun pid hp => he ▸ hi.2 pid hp⟩) a ha

private theorem completion_bad (initial : FlatTable × FlatTable) (P Q)
    (safe : ∀ h w, P h w → CompletionSafe initial h) (message : String) :
    PrefixEnsures P (CompletionSafe initial) (liftPrefix (invariant message : M α)) Q := by
  apply PrefixEnsures.lift _ safe
  intro h w x v hi hr
  cases hr

private theorem state_pure (initial : FlatTable × FlatTable) (x : α) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial) (pure x)
      (fun _ => CompletionState initial) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)

private theorem acquired_out (initial : FlatTable × FlatTable) (a : PeerAttrs)
    (peer out : Option PeerId) (ret : Int) :
    PrefixEnsures (CompletionAcquired initial peer) (CompletionSafe initial)
      (peerConfigOutObserved a out ret) (fun _ => CompletionState initial) :=
  (peerConfigOutObserved_preserves initial a out ret).consequence
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem acquired_create (initial : FlatTable × FlatTable) (peer : Option PeerId)
    (key : Key) (psk : Option Key) :
    PrefixEnsures (CompletionAcquired initial peer) (CompletionSafe initial)
      (liftPrefix (peerCreate key psk)) (CompletionCreated initial) :=
  (peerCreate_completion initial key psk).consequence
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem acquired_update (initial : FlatTable × FlatTable) (a : PeerAttrs)
    (shape : PeerAddressShape a) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) :
    PrefixEnsures (CompletionAcquired initial peer) (CompletionSafe initial)
      (do
        let some pid := peer | liftPrefix (invariant "set_peer without a peer")
        peerConfigUpdateObserved a peer flags psk pid)
      (fun _ => CompletionState initial) := by
  cases peer with
  | none => exact completion_bad initial _ _ (fun _ _ hi => hi.1.1) _
  | some pid =>
    exact (peerConfigUpdateObserved_spec initial a shape (some pid) flags psk pid).consequence
      (fun _ _ hi => ⟨hi.1, hi.2 pid rfl⟩) (fun _ _ _ hi => hi)

private theorem state_bad (initial : FlatTable × FlatTable) (message : String) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (liftPrefix (invariant message : M α)) (fun _ => CompletionState initial) :=
  completion_bad initial _ _ (fun _ _ hi => hi.1) message

private theorem peerCommandAcquiredObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) (publicKey : Key)
    (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    PrefixEnsures (CompletionAcquired initial peer) (CompletionSafe initial)
      (peerCommandAcquiredObserved a publicKey psk flags peer) (fun _ => CompletionState initial) := by
  unfold peerCommandAcquiredObserved
  apply PrefixEnsures.bind (completion_acquired_same initial peer _ (routing_kernel _ (sameKernel_branch _ _)))
  intro found
  split
  · apply PrefixEnsures.bind (completion_acquired_same initial peer _ (routing_kernel _ (sameKernel_branch _ _)))
    intro refused
    split
    · exact acquired_out initial a peer none 0
    · apply PrefixEnsures.bind (completion_acquired_same initial peer _ (routing_kernel _ getDev_sameKernel))
      intro d
      apply PrefixEnsures.bind (completion_acquired_same initial peer _ (routing_kernel _
        (andM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _))))
      intro own
      split
      · exact acquired_out initial a peer none 0
      · apply PrefixEnsures.bind (acquired_create initial peer publicKey psk)
        intro result
        cases result with
        | error err =>
          apply PrefixEnsures.bind (completion_state_same initial _ (routing_kernel _ (sameKernel_branch _ _)))
          intro _
          exact peerConfigOutObserved_preserves initial a none err
        | ok pid =>
          apply PrefixEnsures.bind (completion_lift_same initial pid _ (routing_kernel _ (sameKernel_branch _ _)))
          intro _
          apply PrefixEnsures.bind (completion_lift_same initial pid _ (peerGet_routing pid))
          intro _
          exact peerConfigUpdateObserved_spec initial a shape (some pid)
            (flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS) psk pid
  · exact acquired_update initial a shape peer flags psk

theorem setPeerCmdObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial)
      (setPeerCmdObserved a) (fun _ => CompletionState initial) := by
  unfold setPeerCmdObserved
  repeat' first
    | with_reducible exact peerCommandAcquiredObserved_spec initial a shape _ _ _ _
    | with_reducible exact peerConfigOutObserved_preserves initial a _ _
    | with_reducible exact state_bad initial _
    | with_reducible exact state_pure initial _
    | with_reducible exact pubkeyLookup_completion initial _
    | (solve | with_reducible apply completion_state_same initial; apply routing_kernel; repeat' first | with_reducible exact sameKernel_branch _ _ | with_reducible exact getDev_sameKernel | with_reducible apply andM_sameKernel)
    | with_reducible apply PrefixEnsures.bind
    | with_reducible apply PrefixEnsures.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.Configuration
