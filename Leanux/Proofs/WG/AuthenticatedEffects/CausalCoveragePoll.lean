import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageCandidate
import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackPoll
import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayAuthorizedPoll
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageReceive
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames

/-! The actual successful replay branch certifies its own candidate before
consume. Rejected and unfinished checks cannot authorize effects. The actual
GRO callback separately establishes its inherited packet scope. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues.RxJoint TransportReplay
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem poll_source
    (consumer : PeerId → RxPacket → Endpoint → PrefixM Event (Option (List UInt8)))
    (receive : GroOccurrence.Buffer → GroOccurrence.Entry → PrefixM Event GroOccurrence.Buffer)
    (flush : GroOccurrence.Buffer → PrefixM Event Unit)
    (hu : ∀ pid pkt ep, ProductGuarded (consumer pid pkt ep))
    (hr : ∀ gro entry, ProductClosed (receive gro entry))
    (hf : ∀ gro, ProductClosed (flush gro))
    (pid : PeerId) (budget : Nat) :
    ProductAt frames (GroOccurrencePoll.sourceWith (fun action => liftWGObserver (liftWGPrefix action))
      (CausalSources.candidateEnter Event.scope) (CausalScope.leavePrefix Event.scope)
      (TransportDriver.counter replay) consumer receive flush pid budget) := by
  change PrefixEnsures (fun h (_ : World) => Inv frames h) Safe
    (GroOccurrencePoll.sourceWith (fun action => liftPrefix (liftWG action))
      (CausalSources.candidateEnter Event.scope) (CausalScope.leavePrefix Event.scope)
      (TransportDriver.counter replay) consumer receive flush pid budget)
    (fun _ h (_ : World) => Inv frames h)
  unfold GroOccurrencePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (replay_callback consumer
       apply candidate_consume_bind (success := by simp_all)
       exact hu _ _ _ _ (by simp))
    | (replay_callback receive; exact hr _ _ _)
    | (replay_callback flush; exact hf _ _)
    | (rx_phase_head plain CausalSources.candidateEnter; apply candidate_enter_bind)
    | (rx_phase_head plain TransportDriver.counter; apply candidate_counter_bind)
    | (rx_phase_head plain CausalScope.leavePrefix
       first | apply candidate_leave_bind | apply leave_bind)
    | (replay_native_head invariant
       apply GroOccurrencePoll.Witness.stopped
       intro h w ready; first | exact ready.1 | exact ready.1.1)
    | (replay_native_head branch
       apply GroOccurrencePoll.Witness.branch_bind
       · intro h ready; first | exact ready.1 | exact ready.1.1
       intro result equal)
    | (replay_head liftPrefix
       apply GroOccurrencePoll.Witness.native
       intro h ready; first | exact ready.1 | exact ready.1.1)
    | (replay_head Bind.bind; apply GroOccurrencePoll.Witness.flow_bind)
    | (replay_head Pure.pure
       apply PrefixEnsures.pure
       · intro h w ready; first | exact ready.1 | exact ready.1.1
       · intro h w ready; exact ready)
    | (replay_head ForIn.forIn; apply product_forIn)
    | (replay_head ite; apply PrefixEnsures.ite)
    | rx_phase_reduce
    | rx_phase_match
    | rx_phase_intro
    | assumption

private theorem batch_stack (entries : List GroOccurrence.Entry) :
    ProductAt frames (GroOccurrence.stackWith hooks.stackInput (Driver.stackObserved hooks) entries) := by
  unfold GroOccurrence.stackWith
  induction entries with
  | nil => exact product_pure ()
  | cons entry entries ih =>
    exact product_bind (product_scope (.stackInput entry) True.intro _ (fun _ _ live => stack_input entry.bytes live) frames)
      (fun _ => ih)

theorem native_poll (pid : PeerId) (budget : Nat) : ProductAt frames (Driver.nativePollObserved hooks pid budget) := by
  unfold Driver.nativePollObserved GroOccurrencePoll.observed
  rw [show hooks.counterCheck = TransportDriver.counter replay from
    funext fun skb => funext fun packet => StackOrigins.counter_eq skb packet]
  apply poll_source
  · intro peer packet endpoint frames live; exact product_state _ (consume peer packet endpoint live)
  · intro gro entry frames
    exact GroOccurrence.receive_preserves (I := fun h _ => Inv frames h) (S := Safe)
      (fun _ _ ready => ready.1) _ batch_stack gro entry
  · intro gro frames
    exact GroOccurrence.flushAll_preserves (I := fun h _ => Inv frames h) (S := Safe)
      (fun _ _ ready => ready.1) _ batch_stack gro

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
