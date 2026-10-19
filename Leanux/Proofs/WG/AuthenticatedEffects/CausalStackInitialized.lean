import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackPoll
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.AuthenticatedEffects.TransportJournalInitialized
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter

/-! Initialized inherited stack-input authorization is joined against the
same final driver's exact old-event projection. Buffered occurrence identity
survives GRO delay/reordering and internally stopped callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def origin? (event : Event) : Option TransportDriver.OriginEvent :=
  (old? event).bind Journal.origin?

def replay? (event : Event) : Option TransportDriver.Replay :=
  (old? event).bind Journal.replay?

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (execute trace placeholders) []).2 :=
  Driver.initialized_actor_history actors (GroOccurrence.Origins.Safe.empty candidate replay stack?) trace placeholders

theorem initialized_replays (trace : Runner.Trace) (placeholders : Bool) :
    TransportReplay.Safe origin? replay? (runPrefixOuter (execute trace placeholders) []).2 := by
  have authentic := (TransportJournal.initialized_ordered trace placeholders).1
  have projected := congrArg Prod.snd (execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at projected
  intro pre event post position receipt recorded
  cases event with
  | old event =>
    have oldPosition : (runPrefixOuter (Journal.execute trace placeholders) []).2 =
        pre.filterMap old? ++ event :: post.filterMap old? := by
      rw [projected,position]
      simp only [List.filterMap_append,List.filterMap_cons,old?]
    have checked := authentic _ event _ oldPosition receipt recorded
    change TransportReplay.Certified (pre.filterMap fun event => (old? event).bind Journal.origin?) receipt
    simpa only [List.filterMap_filterMap] using checked
  | scope value => cases recorded
  | armed value => cases recorded
  | queued value => cases recorded
  | exchange value => cases recorded
  | keepalivePrepared pid run => cases recorded
  | protocolSocket receipt => cases recorded
  | cookieSocket receipt | cookieConsumed receipt => cases recorded
  | delivery sent => cases recorded

/-- Each initialized stack-input scope inherits its own accepted receive,
including held GRO packets. The successful replay and AEAD publication belong
to the same earlier occurrence, rather than merely matching packet contents. -/
theorem initialized_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (index : Nat) (entry : GroOccurrence.Entry)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.scope (.entered ⟨index,.stackInput entry⟩) :: post) :
    ∃ start receipt rest,
      pre = start ++ [candidate entry.scope entry.skb entry.packet,replay receipt] ++ rest ∧
      entry.scope = start.length ∧ receipt.skb = entry.skb ∧ receipt.packet = entry.packet ∧
      receipt.run.value = true ∧
      TransportReplay.Certified
        ((start ++ [candidate entry.scope entry.skb entry.packet]).filterMap origin?) receipt :=
  GroOccurrence.Origins.stack_authenticated candidate replay stack? origin? replay? (fun _ => rfl)
    (initialized trace placeholders) (initialized_replays trace placeholders) position rfl

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins
