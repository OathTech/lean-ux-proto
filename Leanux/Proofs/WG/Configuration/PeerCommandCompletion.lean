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
    (psk : Option Key) (flags : UInt32) (peer : Option PeerId) : WGPrefix RoutingCompletion Int := do
  let mut flags := flags
  let mut peer := peer
  if ← liftWGPrefix (branch .peerNotFound peer.isNone) then
    if ← liftWGPrefix (branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0)) then
      return ← peerConfigOutObserved a none 0
    flags := flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS
    let id := (← liftWGPrefix getDev).staticIdentity
    if ← liftWGPrefix (WG.andM (branch .peerSelfHasIdentity id.hasIdentity) (branch .peerSelfKeyMatch (publicKey == id.staticPublic))) then
      return ← peerConfigOutObserved a none 0
    match ← liftWGPrefix (peerCreate publicKey psk) with
    | .error e =>
      _ ← liftWGPrefix (branch .peerCreateErr true)
      return ← peerConfigOutObserved a none e
    | .ok pid =>
      _ ← liftWGPrefix (branch .peerCreateErr false)
      liftWGPrefix (peerGet pid)
      peer := some pid
  let some pid := peer | liftWGPrefix (invariant "set_peer without a peer")
  peerConfigUpdateObserved a peer flags psk pid

def setPeerCmdObserved (a : PeerAttrs) : WGPrefix RoutingCompletion Int := do
  if !(← liftWGPrefix (WG.andM (branch .peerHasPubkey a.publicKey.isSome) (branch .peerPubkeyLen true))) then
    return ← peerConfigOutObserved a none (-EINVAL)
  let some publicKey := a.publicKey | liftWGPrefix (invariant "unreachable")
  let psk ← do
    if ← liftWGPrefix (WG.andM (branch .peerHasPsk a.presharedKey.isSome) (branch .peerPskLen true)) then pure a.presharedKey
    else pure none
  let mut flags : UInt32 := 0
  if ← liftWGPrefix (branch .peerHasFlags a.flags.isSome) then flags := a.flags.getD 0
  if ← liftWGPrefix (branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0)) then return ← peerConfigOutObserved a none (-EOPNOTSUPP)
  if ← liftWGPrefix (branch .peerHasProtocol a.protocolVersion.isSome) then
    if ← liftWGPrefix (branch .peerBadProtocol (a.protocolVersion != some 1)) then return ← peerConfigOutObserved a none (-EPFNOSUPPORT)
  let mut peer ← liftWGPrefix (pubkeyLookup publicKey)
  peerCommandAcquiredObserved a publicKey psk flags peer

theorem setPeerCmdObserved_erases (a : PeerAttrs) :
    ErasesStatePrefix (setPeerCmdObserved a) (setPeerCmd a) := by
  rw [← setPeerCmd_source]
  unfold setPeerCmdObserved peerCommandAcquiredObserved setPeerCmdSource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head peerConfigUpdateObserved; exact peerConfigUpdateObserved_erases _ _ _ _ _)
    | (maintenance_head peerConfigOutObserved; exact peerConfigOutObserved_erases _ _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

private theorem completion_same_wg (initial : FlatTable × FlatTable)
    (P : List RoutingCompletion → WGWorld → Prop)
    (safe : ∀ h w, P h w → CompletionSafe initial h)
    (frame : ∀ h w v, routingView v = routingView w → P h w → P h v)
    (a : WG.M α) (ha : SameView routingView a) :
    StatePrefixEnsures (fun h w _ => P h w) (CompletionSafe initial) (liftWGPrefix a) (fun _ h w _ => P h w) := by
  apply StatePrefixEnsures.lift a (fun h w _ hi => safe h w hi)
  intro h w ambient x v ambientNext hi hr
  exact frame h w v ((ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambientNext hr) hi

private theorem completion_state_same_wg (initial : FlatTable × FlatTable)
    (a : WG.M α) (ha : SameView routingView a) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (liftWGPrefix a) (fun _ h w _ => CompletionState initial h w) :=
  completion_same_wg initial _ (fun _ _ hi => hi.1)
    (fun _ _ _ he hi => ⟨hi.1, he ▸ hi.2⟩) a ha

private theorem completion_acquired_same_wg (initial : FlatTable × FlatTable) (peer : Option PeerId)
    (a : WG.M α) (ha : SameView routingView a) :
    StatePrefixEnsures (fun h w _ => CompletionAcquired initial peer h w) (CompletionSafe initial)
      (liftWGPrefix a) (fun _ h w _ => CompletionAcquired initial peer h w) :=
  completion_same_wg initial _ (fun _ _ hi => hi.1.1)
    (fun _ _ _ he hi => ⟨⟨hi.1.1, he ▸ hi.1.2⟩, fun pid hp => he ▸ hi.2 pid hp⟩) a ha

private theorem completion_bad_wg (initial : FlatTable × FlatTable) (P : List RoutingCompletion → WGWorld → Prop)
    (Q : α → List RoutingCompletion → WGWorld → Prop)
    (safe : ∀ h w, P h w → CompletionSafe initial h) (message : String) :
    StatePrefixEnsures (fun h w _ => P h w) (CompletionSafe initial) (liftWGPrefix (invariant message : WG.M α)) (fun x h w _ => Q x h w) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => safe h w hi)
  intro h w ambient x v ambientNext hi hr
  cases hr

private theorem state_pure_wg (initial : FlatTable × FlatTable) (x : α) :
    StatePrefixEnsures (fun h w (_ : Ambient) => CompletionState initial h w) (CompletionSafe initial) (pure x)
      (fun _ h w _ => CompletionState initial h w) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem acquired_out (initial : FlatTable × FlatTable) (a : PeerAttrs)
    (peer out : Option PeerId) (ret : Int) :
    StatePrefixEnsures (fun h w _ => CompletionAcquired initial peer h w) (CompletionSafe initial)
      (peerConfigOutObserved a out ret) (fun _ h w _ => CompletionState initial h w) :=
  (peerConfigOutObserved_preserves initial a out ret).consequence
    (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

private theorem acquired_create (initial : FlatTable × FlatTable) (peer : Option PeerId)
    (key : Key) (psk : Option Key) :
    StatePrefixEnsures (fun h w _ => CompletionAcquired initial peer h w) (CompletionSafe initial)
      (liftWGPrefix (peerCreate key psk)) (fun result h w _ => CompletionCreated initial result h w) :=
  (peerCreate_completion initial key psk).consequence
    (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

private theorem acquired_update (initial : FlatTable × FlatTable) (a : PeerAttrs)
    (shape : PeerAddressShape a) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) :
    StatePrefixEnsures (fun h w _ => CompletionAcquired initial peer h w) (CompletionSafe initial)
      (do
        let some pid := peer | liftWGPrefix (invariant "set_peer without a peer")
        peerConfigUpdateObserved a peer flags psk pid)
      (fun _ h w _ => CompletionState initial h w) := by
  cases peer with
  | none => exact completion_bad_wg initial _ _ (fun _ _ hi => hi.1.1) _
  | some pid =>
    exact (peerConfigUpdateObserved_spec initial a shape (some pid) flags psk pid).consequence
      (fun _ _ _ hi => ⟨hi.1, hi.2 pid rfl⟩) (fun _ _ _ _ hi => hi)

private theorem state_bad_wg (initial : FlatTable × FlatTable) (message : String) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (liftWGPrefix (invariant message : WG.M α)) (fun _ h w _ => CompletionState initial h w) :=
  completion_bad_wg initial _ _ (fun _ _ hi => hi.1) message

private theorem peerCommandAcquiredObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) (publicKey : Key)
    (psk : Option Key) (flags : UInt32) (peer : Option PeerId) :
    StatePrefixEnsures (fun h w _ => CompletionAcquired initial peer h w) (CompletionSafe initial)
      (peerCommandAcquiredObserved a publicKey psk flags peer) (fun _ h w _ => CompletionState initial h w) := by
  have hb (decision : Decision) (value : Bool) : SameView routingView (branch decision value) :=
    fun initial => hoare_liftAmbient (AmbientM.branch decision value) (fun w => routingView w = initial)

  unfold peerCommandAcquiredObserved
  apply StatePrefixEnsures.bind (completion_acquired_same_wg initial peer _ (hb _ _))
  intro found
  split
  · apply StatePrefixEnsures.bind (completion_acquired_same_wg initial peer _ (hb _ _))
    intro refused
    split
    · exact acquired_out initial a peer none 0
    · apply StatePrefixEnsures.bind (completion_acquired_same_wg initial peer _ (getDev_sameWGStore.of_factor (fun store => store.dev.map routingState) routingView (fun _ => rfl)))
      intro d
      apply StatePrefixEnsures.bind (completion_acquired_same_wg initial peer _ (DumpComposition.andM_sameView _ _ (hb _ _) (hb _ _)))
      intro own
      split
      · exact acquired_out initial a peer none 0
      · apply StatePrefixEnsures.bind (acquired_create initial peer publicKey psk)
        intro result
        cases result with
        | error err =>
          apply StatePrefixEnsures.bind (completion_state_same_wg initial _ (hb _ _))
          intro _
          exact peerConfigOutObserved_preserves initial a none err
        | ok pid =>
          apply StatePrefixEnsures.bind (completion_lift_same_wg initial pid _ (hb _ _))
          intro _
          apply StatePrefixEnsures.bind (completion_lift_same_wg initial pid _ (peerGet_routing pid))
          intro _
          exact peerConfigUpdateObserved_spec initial a shape (some pid)
            (flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS) psk pid
  · exact acquired_update initial a shape peer flags psk

theorem setPeerCmdObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (setPeerCmdObserved a) (fun _ h w _ => CompletionState initial h w) := by
  have hb (decision : Decision) (value : Bool) : SameView routingView (branch decision value) :=
    fun initial => hoare_liftAmbient (AmbientM.branch decision value) (fun w => routingView w = initial)

  unfold setPeerCmdObserved
  repeat' first
    | (maintenance_head peerCommandAcquiredObserved; exact peerCommandAcquiredObserved_spec initial a shape _ _ _ _)
    | (maintenance_head peerConfigOutObserved; exact peerConfigOutObserved_preserves initial a _ _)
    | (maintenance_lift_action_head invariant; exact state_bad_wg initial _)
    | (maintenance_lift_action_head pubkeyLookup; exact pubkeyLookup_completion initial _)
    | (maintenance_lift_action_head branch; exact completion_state_same_wg initial _ (hb _ _))
    | (maintenance_lift_action_head WG.andM; exact completion_state_same_wg initial _ (DumpComposition.andM_sameView _ _ (hb _ _) (hb _ _)))
    | (maintenance_head Pure.pure; exact state_pure_wg initial _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind)
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)

private theorem completion_same (initial : FlatTable × FlatTable)
    (P : List RoutingCompletion → World → Prop)
    (safe : ∀ h w, P h w → CompletionSafe initial h)
    (frame : ∀ h w v, routingView v.wg = routingView w.wg → P h w → P h v)
    (a : Leanux.M α) (ha : SameView (fun w : World => routingView w.wg) a) :
    PrefixEnsures P (CompletionSafe initial) (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a safe
  intro h w x v hi hr
  exact frame h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

private theorem completion_bad (initial : FlatTable × FlatTable) (P Q)
    (safe : ∀ h w, P h w → CompletionSafe initial h) (message : String) :
    PrefixEnsures P (CompletionSafe initial) (liftPrefix (invariant message : Leanux.M α)) Q := by
  apply PrefixEnsures.lift _ safe
  intro h w x v hi hr
  cases hr

private theorem completion_state_same (initial : FlatTable × FlatTable)
    (a : Leanux.M α) (ha : SameView (fun w : World => routingView w.wg) a) :
    PrefixEnsures (fun h (w : World) => CompletionState initial h w.wg) (CompletionSafe initial)
      (liftPrefix a) (fun _ h (w : World) => CompletionState initial h w.wg) :=
  completion_same initial _ (fun _ _ hi => hi.1)
    (fun _ _ _ he hi => ⟨hi.1, he ▸ hi.2⟩) a ha


private theorem completion_acquired_same (initial : FlatTable × FlatTable) (peer : Option PeerId)
    (a : Leanux.M α) (ha : SameView (fun w : World => routingView w.wg) a) :
    PrefixEnsures (fun h (w : World) => CompletionAcquired initial peer h w.wg) (CompletionSafe initial)
      (liftPrefix a) (fun _ h (w : World) => CompletionAcquired initial peer h w.wg) :=
  completion_same initial _ (fun _ _ hi => hi.1.1)
    (fun _ _ _ he hi => ⟨⟨hi.1.1, he ▸ hi.1.2⟩, fun pid hp => he ▸ hi.2 pid hp⟩) a ha


private theorem state_pure (initial : FlatTable × FlatTable) (x : α) :
    PrefixEnsures (fun h (w : World) => CompletionState initial h w.wg) (CompletionSafe initial) (pure x)
      (fun _ h (w : World) => CompletionState initial h w.wg) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)


private theorem state_bad (initial : FlatTable × FlatTable) (message : String) :
    PrefixEnsures (fun h (w : World) => CompletionState initial h w.wg) (CompletionSafe initial)
      (liftPrefix (invariant message : Leanux.M α)) (fun _ h (w : World) => CompletionState initial h w.wg) :=
  completion_bad initial _ _ (fun _ _ hi => hi.1) message


end Leanux.Proofs.WG.Configuration
