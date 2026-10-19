import Leanux.Proofs.WG.AuthenticatedEffects.QueuedOccurrences
import Leanux.Proofs.WG.AuthenticatedEffects.SendEffectsSource

/-! Native source contracts for appending and consuming exact queued-work
occurrences. Queue membership is supplied by the actual dispatch/drain caller;
these lemmas never authorize an arbitrary invocation of the flushed worker. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.QueuedOccurrences
open Leanux Leanux.WG Leanux.Proofs.Logged

def Inv (record : TimerEffects.Queued Cause → E) (h : List E) (w : WGWorld) : Prop :=
  ∃ tickets, Carrier record h tickets w

theorem receipt_preserves (record : TimerEffects.Queued Cause → E) (cause : Cause) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Inv record h w) (fun _ => True)
      (TimerEffects.queueReceipt record cause pid) := by
  intro w a h hi
  obtain ⟨tickets,carrier⟩ := hi
  change ∃ suffix, (runWGPrefix (TimerEffects.queueReceipt record cause pid) w a h).2 = h ++ suffix ∧
    True ∧ match (runWGPrefix (TimerEffects.queueReceipt record cause pid) w a h).1 with
      | .error _ => True
      | .ok ((_,v),_) => Inv record (runWGPrefix (TimerEffects.queueReceipt record cause pid) w a h).2 v
  rw [TimerEffects.queueReceipt,runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  cases run : ((modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}).run w).run a with
  | error stop => exact ⟨[],by simp,True.intro,True.intro⟩
  | ok result =>
    rcases result with ⟨⟨value,v⟩,b⟩
    cases value
    let receipt : TimerEffects.Queued Cause := ⟨cause,pid,⟨(),w,v,a,b⟩⟩
    refine ⟨[record receipt],rfl,True.intro,?_⟩
    by_cases device : w.dev.isSome
    · exact ⟨tickets ++ [⟨h.length,receipt⟩],carrier.enqueue receipt run device⟩
    · have before : w.dev = none := by
        cases hd : w.dev with
        | none => rfl
        | some d => simp [hd] at device
      have after : v.dev = none := by simpa only [receipt,before,Option.map_none] using native_append receipt run
      exact ⟨tickets,(carrier.append [record receipt]).frame (by simp only [queue,before,after])⟩

theorem flushed_normal (record : TimerEffects.Queued Cause → E) (pid : PeerId)
    (body : WGPrefix E Unit) (erases : ErasesStatePrefix body (runFlushedSendWork pid))
    (appends : StateAppends body) (w v : WGWorld) (a b : Ambient) (h history : List E)
    (tickets : List (Ticket Cause)) (carrier : Carrier record h tickets w)
    (present : pid ∈ queue w) (run : runWGPrefix body w a h = (.ok (((),v),b),history)) :
    ∃ ticket rest, Selected tickets pid ticket rest ∧ ticket.Valid record h ∧
      Carrier record history rest v := by
  obtain ⟨ticket,rest,selected⟩ := select_exists tickets pid (carrier.1 ▸ present)
  have native : ((runFlushedSendWork pid).run w).run a = .ok (((),v),b) :=
    (erases w a h).symm.trans (congrArg Prod.fst run)
  obtain ⟨valid,after⟩ := carrier.dequeue selected (SendWorkCauses.flushed_queue pid w v a b native)
  obtain ⟨suffix,grown⟩ := appends w a h
  change (runWGPrefix body w a h).2 = h ++ suffix at grown
  rw [run] at grown
  refine ⟨ticket,rest,selected,valid,?_⟩
  change history = h ++ suffix at grown
  rw [grown]
  exact after.append suffix

/-- The lexical entry retains the exact earlier append occurrence through a
later Stop. Authentication of that receipt's cause and initialized carrier
transport are separate obligations, not assumptions hidden in a root label. -/
theorem scope_ticket (record : TimerEffects.Queued Cause → E)
    (scopeRecord : CausalScope.Event CausalSources.Cause → E) (pid : PeerId)
    (body : WGPrefix E α) (appends : StateAppends body)
    (w : WGWorld) (a : Ambient) (h : List E) (tickets : List (Ticket Cause))
    (carrier : Carrier record h tickets w) (present : pid ∈ queue w) :
    ∃ ticket rest before after suffix,
      Selected tickets pid ticket rest ∧ ticket.peer = pid ∧
      h = before ++ record ticket.receipt :: after ∧ before.length = ticket.index ∧
      ticket.receipt.Valid ∧
      (runWGPrefix (CausalSources.workScope scopeRecord pid body) w a h).2 =
        h ++ scopeRecord (.entered ⟨h.length,.sendWork pid (CausalSources.sendEntry pid w)⟩) :: suffix := by
  obtain ⟨ticket,rest,before,after,selected,peer,position,index,valid⟩ := carrier.selected present
  obtain ⟨suffix,entry⟩ := CausalSources.workScope_entry scopeRecord pid body appends w a h
  exact ⟨ticket,rest,before,after,suffix,selected,peer,position,index,valid,entry⟩

end Leanux.Proofs.WG.AuthenticatedEffects.QueuedOccurrences
