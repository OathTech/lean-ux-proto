import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageOuter
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackInitialized

/-! No actual initialized delayed effect or TX allocation is left without a
lexical context. These positions belong to the final journal, not an erased
history or an arbitrary native invocation. Authorization remains separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem initialized_present (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (event : Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ event :: after)
    (relevant : Protected event) : Present before :=
  (initialized trace placeholders before event after position relevant).1

theorem arm_context (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (receipt : TimerEffects.Arm Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .armed receipt :: after) :
    ∃ token, receipt.cause = .ok (some token) ∧ CausalScope.current scope? before = .ok (some token) := by
  obtain ⟨token,current⟩ := initialized_present trace placeholders before after (.armed receipt) position True.intro
  exact ⟨token,(Receipts.initialized_arm trace placeholders before after receipt position).2.trans current,current⟩

theorem queue_context (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (receipt : TimerEffects.Queued Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .queued receipt :: after) :
    ∃ token, receipt.cause = .ok (some token) ∧ CausalScope.current scope? before = .ok (some token) := by
  obtain ⟨token,current⟩ := initialized_present trace placeholders before after (.queued receipt) position True.intro
  exact ⟨token,(Receipts.initialized_queue trace placeholders before after receipt position).2.trans current,current⟩

theorem allocation_context (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (packets : List DataPacket) (run : WGRunWitness (List SkbId))
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .old (.allocated packets run) :: after) :
    Present before :=
  initialized_present trace placeholders before after (.old (.allocated packets run)) position True.intro

/-- A candidate token at a protected effect names its own immediately checked
receive occurrence. Entry alone supplies no authorization: this conclusion uses
the successful native counter branch of that same initialized execution. -/
theorem candidate_accepted (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (event : Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ event :: after)
    (relevant : Protected event) (index : Nat) (skb : SkbId) (packet : RxPacket)
    (current : CausalScope.current scope? before = .ok (some ⟨index,.candidate skb packet⟩)) :
    GroOccurrence.Accepted candidate replay ⟨index,skb,packet,[]⟩ before :=
  (initialized trace placeholders before event after position relevant).2 _ current

/-- A protected timer/work/allocation effect under a receive candidate has its
own earlier successful native replay check and AEAD publication in this exact
final journal, even when a later operation stops. -/
theorem candidate_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (event : Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ event :: after)
    (relevant : Protected event) (index : Nat) (skb : SkbId) (packet : RxPacket)
    (current : CausalScope.current scope? before = .ok (some ⟨index,.candidate skb packet⟩)) :
    ∃ start receipt rest,
      before = start ++ [candidate index skb packet,replay receipt] ++ rest ∧
      index = start.length ∧ receipt.skb = skb ∧ receipt.packet = packet ∧ receipt.run.value = true ∧
      TransportReplay.Certified
        ((start ++ [candidate index skb packet]).filterMap StackOrigins.origin?) receipt := by
  have accepted := candidate_accepted trace placeholders before after event position relevant index skb packet current
  have prefixSafe : TransportReplay.Safe StackOrigins.origin? StackOrigins.replay? before := by
    intro pre value post decomposition
    apply StackOrigins.initialized_replays trace placeholders pre value (post ++ event :: after)
    simp only [position,decomposition,List.append_assoc,List.cons_append]
  exact accepted.authenticated StackOrigins.origin? StackOrigins.replay? (fun _ => rfl) prefixSafe

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
