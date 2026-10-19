import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackActors

/-! The final journal's actual native poll establishes inherited stack
origins at each packet callback, including held GRO packets and Stop prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem counter_eq (skb : SkbId) (packet : RxPacket) :
    hooks.counterCheck skb packet = TransportDriver.counter replay skb packet := by
  funext w h
  change runPrefix (focusPrefix Event.old old? (TransportDriver.counter Journal.Event.replay skb packet)) w h =
    runPrefix (TransportDriver.counter replay skb packet) w h
  change ((runPrefix (TransportDriver.counter Journal.Event.replay skb packet) w (h.filterMap old?)).1,
    h ++ ((runPrefix (TransportDriver.counter Journal.Event.replay skb packet) w (h.filterMap old?)).2.drop
      (h.filterMap old?).length).map Event.old) = _
  rw [TransportDriver.counter_run,TransportDriver.counter_run]
  cases (liftWG (counterValidate packet.keypair packet.nonce)).run w with
  | error stop => simp only [List.drop_length,List.map_nil,List.append_nil]
  | ok result =>
    rcases result with ⟨value,v⟩
    simp only [List.drop_left,List.map_cons,List.map_nil]
    rfl

theorem poll (pid : PeerId) (budget : Nat) :
    Driver.ProductHistorySafe Safe (Driver.nativePollObserved hooks pid budget) := by
  have counters : hooks.counterCheck = TransportDriver.counter replay :=
    funext fun skb => funext fun packet => counter_eq skb packet
  unfold Driver.nativePollObserved
  rw [counters]
  exact GroOccurrence.Origins.observed_checked candidate replay stack? Event.scope CausalSources.Cause.stackInput
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    hooks.candidateLeave (fun peer packet endpoint => liftWGObserver (Driver.consumeObserved hooks peer packet endpoint))
    (Driver.stackObserved hooks) core.candidateLeave
    (fun peer packet endpoint => (Driver.consume_history core peer packet endpoint).liftWGObserver)
    (Driver.stack_history core) pid budget

theorem actors : Driver.ActorHistorySafe Safe hooks where
  toActorCoreHistorySafe := core
  nativePoll := poll

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins
