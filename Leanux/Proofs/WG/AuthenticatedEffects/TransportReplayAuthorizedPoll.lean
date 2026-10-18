import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayAcceptance

/-! The same native poll delivers only its immediately preceding successful
counter receipt to the consumer, after the actual peer and endpoint guards. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues RxJoint
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {record : TransportDriver.Replay → E}
  {pkt : RxPacket} {result : Bool}

private theorem flow_bind (g : PrefixM E α) (f : α → PrefixM E β)
    (hg : PrefixPreserves P S g) (hf : ∀ x, PrefixEnsures P S (f x) Q) :
    PrefixEnsures P S (g >>= f) Q := PrefixEnsures.bind hg hf

private theorem counter_cleanup (kp : Option KeypairId) (now : Bool) (f : Unit → PrefixM E α)
    (hf : PrefixEnsures (Inv origin replay) (Safe origin replay)
      (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q) :
    PrefixEnsures (AtCounter origin replay record pkt result) (Safe origin replay)
      (liftPrefix (liftWG (keypairPut kp now)) >>= f) Q :=
  hf.consequence (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem consume_entry
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (hc : ∀ pid pkt ep, pkt.peer = pid →
      PrefixEnsures (AtCounter origin replay record pkt true) (Safe origin replay)
        (consume pid pkt ep) (fun _ => Inv origin replay))
    (pid : PeerId) (ep : Endpoint) (accepted : result = true) (peer : pkt.peer = pid) :
    PrefixEnsures (AtCounter origin replay record pkt result) (Safe origin replay)
      (consume pid pkt ep) (fun _ => Inv origin replay) := by
  subst result
  exact hc pid pkt ep peer

private theorem consume_bind
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (hc : ∀ pid pkt ep, pkt.peer = pid →
      PrefixEnsures (AtCounter origin replay record pkt true) (Safe origin replay)
        (consume pid pkt ep) (fun _ => Inv origin replay))
    (pid : PeerId) (ep : Endpoint) (f : Option (List UInt8) → PrefixM E α)
    (accepted : result = true) (peer : pkt.peer = pid)
    (next : ∀ x, PrefixEnsures (Inv origin replay) (Safe origin replay) (f x) Q) :
    PrefixEnsures (AtCounter origin replay record pkt result) (Safe origin replay)
      (consume pid pkt ep >>= f) Q :=
  PrefixEnsures.bind (consume_entry consume hc pid ep accepted peer) next

open Lean Meta Elab Tactic in
elab "replay_callback " name:ident : tactic => withMainContext do
  let target ← withReducible (whnf (← getMainTarget))
  unless target.isAppOf ``PrefixEnsures do throwError "not a prefix contract"
  let mut action := target.getAppArgs[target.getAppArgs.size - 2]!
  if action.isAppOf ``Bind.bind then action := action.getAppArgs[action.getAppArgs.size - 2]!
  let callback ← getFVarId name
  unless action.getAppFn == .fvar callback do throwError "another callback"

private theorem ambient_rx (action : AmbientM α) :
    SameView RxDisposition.nativeRxStore (MonadLift.monadLift action : WG.M α) :=
  fun initial => hoare_liftAmbient action (fun w => RxDisposition.nativeRxStore w = initial)

theorem poll_authorized (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroState → List UInt8 → PrefixM E GroState) (flush : GroState → PrefixM E Unit)
    (hc : ∀ pid pkt ep, pkt.peer = pid →
      PrefixEnsures (AtCounter origin replay record pkt true) (Safe origin replay)
        (consume pid pkt ep) (fun _ => Inv origin replay))
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
    | (replay_callback consume; apply consume_bind consume hc
       · simp_all
       · simp_all)
    | with_reducible exact hr _ _
    | with_reducible exact hf _
    | (replay_native_head branch; with_reducible apply state_bind)
    | (replay_native_head branch; with_reducible apply invalid_bind)
    | (rx_phase_head plain TransportDriver.counter
       with_reducible apply PrefixEnsures.bind (counter_returned origin replay record inverse quiet _ _
        (by apply crypted_of_test; simp_all)))
    | (replay_native_head keypairPut; apply counter_cleanup)
    | replay_poll_step
    | (replay_head liftPrefix
       first
       | solve | rx_phase_head plain keypairPut; apply native; intro h; exact TransportPublication.keypairPut_preserves _ _ h
       | solve | rx_phase_head plain freeRxSkb; apply native; intro h; exact TransportPublication.freeRxSkb_preserves _ h
       | solve | apply native_rx; replay_native_frame
       | solve | apply picked_native; replay_native_frame
       | solve | apply atCounter_native; replay_native_frame)
    | (replay_head Bind.bind; apply flow_bind)
    | (replay_head ForIn.forIn; apply PrefixPreserves.forIn)
    | exact fun (h : List E) (w : World) (hi : Inv origin replay h w) => hi.2
    | (rx_phase_intro; try dsimp only)
  all_goals exact native_rx _ (ambient_rx _)

end Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
