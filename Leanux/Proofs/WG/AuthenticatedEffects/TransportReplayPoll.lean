import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayPrepare
import Leanux.Proofs.WG.AuthenticatedEffects.IndexedPollSource

/-! Packet selection, native guards and replay authentication compose in the
actual shared poll source, before endpoint/confirmation/staged-send callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues RxJoint
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option pp.structureInstances false
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {skb : SkbId} {pkt : RxPacket}

private theorem ambient_rx (action : AmbientM α) :
    SameView RxDisposition.nativeRxStore (MonadLift.monadLift action : WG.M α) :=
  fun initial => hoare_liftAmbient action (fun w => RxDisposition.nativeRxStore w = initial)

macro "replay_native_frame" : tactic => `(tactic| (
  try simp (config := {zeta := false}) only [WG.andM,branch,invariant,unsupported]
  repeat' first
    | (snapshot_head getPeer; exact TransportPublication.getPeer_rx _)
    | (snapshot_head setPeer; exact TransportPublication.setPeer_rx _ _)
    | (snapshot_head getRxSkb; exact TransportPublication.getRxSkb_rx _)
    | (snapshot_head PrevQueue.peek; exact TransportPublication.store_rx _ (prevQueuePeek_sameWGStore _))
    | (snapshot_head endpointFromSkb; exact TransportPublication.store_rx _ (endpointFromSkb_sameWGStore _))
    | (snapshot_head getDev; exact TransportPublication.store_rx _ getDev_sameWGStore)
    | (snapshot_head peerPut; exact RxCredits.peerPut_rxView _)
    | (snapshot_head keypairPut; exact
        ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keyPay) _ _).factor Prod.snd)
    | (first | snapshot_head MonadLift.monadLift | snapshot_head MonadLiftT.monadLift
       exact ambient_rx _)
    | (snapshot_head Pure.pure; exact SameView.pure _ _)
    | (snapshot_head Bind.bind; apply SameView.bind)
    | (snapshot_head ite; split)
    | keypairs_intro_forall
    | snapshot_head_reduce
    | snapshot_head_match))

private theorem base_pure (x : α) : Preserves (origin := origin) (replay := replay) (pure x) :=
  PrefixPreserves.pure (fun _ _ hi => hi.2) x

private theorem base_bind (g : PrefixM E α) (f : α → PrefixM E β)
    (hg : Preserves (origin := origin) (replay := replay) g)
    (hf : ∀ x, Preserves (origin := origin) (replay := replay) (f x)) :
    Preserves (origin := origin) (replay := replay) (g >>= f) := hg.bind hf

private theorem picked_bind (g : PrefixM E α) (f : α → PrefixM E β)
    (hg : PrefixPreserves (Picked origin replay skb pkt) (Safe origin replay) g)
    (hf : ∀ x, PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay) (f x) Q) :
    PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay) (g >>= f) Q :=
  PrefixEnsures.bind hg hf

private theorem read_bind (id : SkbId) (f : RxPacket → PrefixM E α)
    (hf : ∀ pkt, PrefixEnsures (Picked origin replay id pkt) (Safe origin replay) (f pkt) Q) :
    PrefixEnsures (Inv origin replay) (Safe origin replay) (liftPrefix (liftWG (getRxSkb id)) >>= f) Q :=
  PrefixEnsures.bind (read_selected id) hf

private theorem cleanup (kp : Option KeypairId) (now : Bool) (f : Unit → PrefixM E α)
    (hf : PrefixEnsures (Inv origin replay) (Safe origin replay)
      (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q) :
    PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay)
      (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q :=
  hf.consequence (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem stop (message : String) (f : Unit → PrefixM E α)
    (safe : ∀ h w, P h w → Safe origin replay h) :
    PrefixEnsures P (Safe origin replay) (liftPrefix (liftWG (invariant message)) >>= f) Q := by
  intro w h hi
  exact ⟨[],by simp only [runPrefix_bind,runPrefix_lift,List.append_nil]; rfl,safe h w hi,True.intro⟩

open Lean Meta Elab Tactic in
elab "replay_native_head " name:ident : tactic => withMainContext do
  let target ← withReducible (whnf (← getMainTarget))
  unless target.isAppOf ``PrefixEnsures do throwError "not PrefixEnsures"
  let args := target.getAppArgs
  let mut action := args[args.size - 2]!
  if action.isAppOf ``Bind.bind then action := action.getAppArgs[action.getAppArgs.size - 2]!
  unless action.isAppOf ``liftPrefix do throwError "not a native prefix lift"
  action := action.getAppArgs.back!
  action ← withReducible (whnf action)
  -- `liftWG` is the concrete product adapter; inspect its unexpanded application.
  unless action.isAppOf ``liftWG do throwError "not a WG product lift"
  let native := action.getAppArgs.back!
  unless native.isAppOf (← resolveGlobalConstNoOverload name) do throwError "another native source"

open Lean Meta Elab Tactic in
elab "replay_head " name:ident : tactic => withMainContext do
  let target ← withReducible (whnf (← getMainTarget))
  unless target.isAppOf ``PrefixEnsures do throwError "not PrefixEnsures"
  let args := target.getAppArgs
  let action := args[args.size - 2]!
  unless action.isAppOf (← resolveGlobalConstNoOverload name) do throwError "another action"

open Lean Meta Elab Tactic in
elab "replay_contract" : tactic => withMainContext do
  let target ← withReducible (whnf (← getMainTarget))
  unless target.isAppOf ``PrefixPreserves do throwError "not an unexpanded preservation contract"
  evalTactic (← `(tactic| change PrefixEnsures _ _ _ (fun _ => _)))

macro "replay_poll_step" : tactic => `(tactic| first
  | replay_contract
  | rx_phase_reduce
  | (replay_native_head invariant; apply stop; intro h w hi; first | exact hi.2 | exact hi.1.2)
  | (replay_native_head getRxSkb; apply read_bind)
  | (replay_native_head keypairPut; apply cleanup)
  | (replay_head Pure.pure; exact base_pure _)
  | (replay_head ite; apply PrefixEnsures.ite)
  | rx_phase_match)

theorem poll_checked (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroState → List UInt8 → PrefixM E GroState) (flush : GroState → PrefixM E Unit)
    (hc : ∀ pid pkt ep, Preserves (origin := origin) (replay := replay) (consume pid pkt ep))
    (hr : ∀ gro bytes, Preserves (origin := origin) (replay := replay) (receive gro bytes))
    (hf : ∀ gro, Preserves (origin := origin) (replay := replay) (flush gro))
    (pid : PeerId) (budget : Nat) :
    Preserves (origin := origin) (replay := replay)
      (IndexedPoll.sourceWith (fun a => liftPrefix (liftWG a)) (TransportDriver.counter record)
        consume receive flush pid budget) := by
  unfold IndexedPoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  change PrefixEnsures (Inv origin replay) (Safe origin replay) _ (fun _ => Inv origin replay)
  repeat' first
    | with_reducible exact hc _ _ _
    | with_reducible exact hr _ _
    | with_reducible exact hf _
    | (replay_native_head branch; with_reducible apply state_bind)
    | (rx_phase_head plain TransportDriver.counter
       with_reducible apply PrefixEnsures.bind (counter_checked origin replay record inverse quiet _ _
        (by apply crypted_of_test; simp_all)))
    | replay_poll_step
    | (replay_head liftPrefix
       first
       | solve | rx_phase_head plain keypairPut; apply native; intro h; exact TransportPublication.keypairPut_preserves _ _ h
       | solve | rx_phase_head plain freeRxSkb; apply native; intro h; exact TransportPublication.freeRxSkb_preserves _ h
       | solve | apply native_rx; replay_native_frame
       | solve | apply picked_native; replay_native_frame)
    | (replay_head Bind.bind; first | apply base_bind | apply picked_bind)
    | (replay_head ForIn.forIn; apply PrefixPreserves.forIn)
    | exact fun (h : List E) (w : World) (hi : Inv origin replay h w) => hi.2
    | (rx_phase_intro; try dsimp only)

  all_goals exact native_rx _ (ambient_rx _)

end Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
