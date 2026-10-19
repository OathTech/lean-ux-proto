import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceEntryProjection
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceRefusal
import Leanux.Proofs.WG.AuthenticatedEffects.RefusalPositiveKeys

/-! Actual cookie-consumer entries inherit initialized resident-peer positivity
from the same final source execution. No entry or reachability premise is added. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

private theorem entry_history (trace : Runner.Trace) (placeholders : Bool) :
    (runPrefixOuter (EntrySource.execute (E := EntryEvent) trace placeholders) []).2 =
      (runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap EntryCausal.entry? := by
  have project := EntryCausal.execute_projects trace placeholders []
  exact congrArg Prod.snd project

theorem final_entries_safe (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap EntryCausal.entry?) := by
  have safe := entry_initialized_safe (E := EntryEvent) trace placeholders
  rwa [entry_history] at safe

theorem final_cookie_entry (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (receipt : CookieConsumption.Receipt)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ CausalJournal.Event.cookieConsumed receipt :: post) :
    Inv receipt.run.before ∧ receipt.Valid := by
  have safe := final_entries_safe trace placeholders
  apply safe (.cookie ⟨receipt.input,receipt.run⟩)
  rw [position,List.filterMap_append,List.filterMap_cons]
  exact List.mem_append_right _ (by simp [EntryCausal.entry?])

theorem final_cookie_refusal (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (receipt : CookieConsumption.Receipt)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ CausalJournal.Event.cookieConsumed receipt :: post)
    (unaccepted : (runWGPrefix (acceptedCookie receipt.input)
      receipt.run.before receipt.run.ambientBefore []).2 = []) :
    ResponseLoan.residents receipt.run.after = ResponseLoan.residents receipt.run.before := by
  obtain ⟨positive,valid⟩ := final_cookie_entry trace placeholders pre post receipt position
  apply ResponseLoan.cookie_refusal receipt.input receipt.run.before receipt.run.after
    receipt.run.ambientBefore receipt.run.ambientAfter (refusal_positive positive) unaccepted
  simpa only [CookieConsumption.Receipt.Valid,WGRunWitness.Valid,
    show receipt.run.value = () from rfl] using valid

theorem final_cookie_refusal_keys (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (receipt : CookieConsumption.Receipt)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ CausalJournal.Event.cookieConsumed receipt :: post)
    (unaccepted : (runWGPrefix (acceptedCookie receipt.input)
      receipt.run.before receipt.run.ambientBefore []).2 = []) :
    ResponseLoan.residentKeys receipt.run.after = ResponseLoan.residentKeys receipt.run.before := by
  obtain ⟨positive,valid⟩ := final_cookie_entry trace placeholders pre post receipt position
  apply ResponseLoan.cookie_refusal_keys receipt.input receipt.run.before receipt.run.after
    receipt.run.ambientBefore receipt.run.ambientAfter (refusal_positive positive) unaccepted
  simpa only [CookieConsumption.Receipt.Valid,WGRunWitness.Valid,
    show receipt.run.value = () from rfl] using valid

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
