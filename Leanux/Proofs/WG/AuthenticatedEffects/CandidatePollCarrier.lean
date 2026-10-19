import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayPoll
import Leanux.Proofs.WG.AuthenticatedEffects.CandidatePollSource

/-! The scoped poll preserves the initialized packet authentication carrier.
Entry must preserve the actual selected skb; exit needs only the ordinary RX
carrier. Neither contract calls a candidate authenticated. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues RxJoint
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {skb : SkbId} {pkt : RxPacket}

private theorem candidate_base_bind {g : PrefixM E α} {f : α → PrefixM E β}
    (hg : Preserves (origin := origin) (replay := replay) g)
    (hf : ∀ x, Preserves (origin := origin) (replay := replay) (f x)) :
    Preserves (origin := origin) (replay := replay) (g >>= f) := hg.bind hf

private theorem candidate_picked_bind {g : PrefixM E α} {f : α → PrefixM E β}
    (hg : PrefixPreserves (Picked origin replay skb pkt) (Safe origin replay) g)
    (hf : ∀ x, PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay) (f x) Q) :
    PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay) (g >>= f) Q :=
  PrefixEnsures.bind hg hf

private theorem candidate_leave_bind {g : PrefixM E α} {f : α → PrefixM E β}
    (hg : Preserves (origin := origin) (replay := replay) g)
    (hf : ∀ x, PrefixEnsures (Inv origin replay) (Safe origin replay) (f x) Q) :
    PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay) (g >>= f) Q :=
  (PrefixEnsures.bind hg hf).consequence (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem candidate_ambient_rx (action : AmbientM α) :
    SameView RxDisposition.nativeRxStore (MonadLift.monadLift action : WG.M α) :=
  fun initial => hoare_liftAmbient action (fun w => RxDisposition.nativeRxStore w = initial)

theorem candidate_poll_checked (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroState → List UInt8 → PrefixM E GroState) (flush : GroState → PrefixM E Unit)
    (he : ∀ skb pkt, PrefixPreserves (Picked origin replay skb pkt) (Safe origin replay) (enter skb pkt))
    (hl : ∀ token, Preserves (origin := origin) (replay := replay) (leave token))
    (hc : ∀ pid pkt ep, Preserves (origin := origin) (replay := replay) (consume pid pkt ep))
    (hr : ∀ gro bytes, Preserves (origin := origin) (replay := replay) (receive gro bytes))
    (hf : ∀ gro, Preserves (origin := origin) (replay := replay) (flush gro))
    (pid : PeerId) (budget : Nat) :
    Preserves (origin := origin) (replay := replay)
      (CandidatePoll.sourceWith (fun a => liftPrefix (liftWG a)) enter leave (TransportDriver.counter record)
        consume receive flush pid budget) := by
  unfold CandidatePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  change PrefixEnsures (Inv origin replay) (Safe origin replay) _ (fun _ => Inv origin replay)
  repeat' first
    | with_reducible exact he _ _
    | with_reducible exact hl _
    | (with_reducible apply PrefixEnsures.bind (he _ _))
    | (with_reducible apply candidate_base_bind (hl _))
    | (with_reducible apply candidate_leave_bind (hl _))
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
    | (replay_head Bind.bind; first | apply candidate_base_bind | apply candidate_picked_bind)
    | (replay_head ForIn.forIn; apply PrefixPreserves.forIn)
    | exact fun (h : List E) (w : World) (hi : Inv origin replay h w) => hi.2
    | (rx_phase_intro; try dsimp only)

  all_goals exact native_rx _ (candidate_ambient_rx _)

end Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
