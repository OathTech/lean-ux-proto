import Leanux.Proofs.WG.AuthenticatedEffects.CausalHandshakePairActors
import Leanux.Proofs.WG.AuthenticatedEffects.CausalContextOrigins
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFreshInitialized
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter

/-! The actual current handshake context is joined to its immediately following
callback and that callback's newest native authentication admission. The scope's
presence remains explicit; this does not authorize malformed or absent contexts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (execute trace placeholders) []).2 :=
  Driver.initialized_actor_history actors True.intro trace placeholders

theorem initialized_pair (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (index : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ .scope (.entered ⟨index,.handshake kind pid⟩) :: post) :
    ∃ rest, post = .old (.handshake (.callback kind pid)) :: rest :=
  (initialized trace placeholders).next pre post index kind pid position

theorem current_callback {history pre post : List Event} (safe : Safe history)
    (effect : Event) (index : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (position : history = pre ++ effect :: post)
    (different : effect ≠ .old (.handshake (.callback kind pid)))
    (current : CausalScope.current scope? pre = .ok (some ⟨index,.handshake kind pid⟩)) :
    ∃ before rest, pre = before ++
      [.scope (.entered ⟨index,.handshake kind pid⟩),.old (.handshake (.callback kind pid))] ++ rest := by
  obtain ⟨before,after,entered⟩ := ContextOrigins.current_entry pre _ current
  have whole : history = before ++ .scope (.entered ⟨index,.handshake kind pid⟩) :: (after ++ effect :: post) := by
    simp only [position,entered,List.append_assoc,List.cons_append]
  obtain ⟨tail,paired⟩ := safe.next before (after ++ effect :: post) index kind pid whole
  cases after with
  | nil =>
    have same : effect = .old (.handshake (.callback kind pid)) := (List.cons.inj paired).1
    exact False.elim (different same)
  | cons first rest =>
    have same : first = .old (.handshake (.callback kind pid)) := (List.cons.inj paired).1
    exact ⟨before,rest,by simpa only [same,List.append_assoc,List.cons_append,List.nil_append] using entered⟩

theorem current_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (effect : Event) (index : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ effect :: post)
    (different : effect ≠ .old (.handshake (.callback kind pid)))
    (current : CausalScope.current scope? pre = .ok (some ⟨index,.handshake kind pid⟩)) :
    ∃ before rest, pre = before ++
      [.scope (.entered ⟨index,.handshake kind pid⟩),.old (.handshake (.callback kind pid))] ++ rest ∧
      HandshakeFresh.Available (before.filterMap handshake?) pid := by
  obtain ⟨before,rest,paired⟩ := current_callback (initialized trace placeholders) effect index kind pid position different current
  refine ⟨before,rest,paired,?_⟩
  have authenticated := HandshakeFresh.callback_latest trace placeholders
    (before ++ [.scope (.entered ⟨index,.handshake kind pid⟩)]) (rest ++ effect :: post) kind pid
    (by simp only [position,paired,List.append_assoc,List.cons_append,List.nil_append])
  simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,handshake?,old?,
    Option.bind_none,Option.toList_none,List.nil_append,List.append_nil] using authenticated

theorem arm_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : TimerEffects.Arm Context)
    (index : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ .armed receipt :: post)
    (cause : receipt.cause = .ok (some ⟨index,.handshake kind pid⟩)) :
    receipt.Valid ∧ ∃ before rest, pre = before ++
      [.scope (.entered ⟨index,.handshake kind pid⟩),.old (.handshake (.callback kind pid))] ++ rest ∧
      HandshakeFresh.Available (before.filterMap handshake?) pid := by
  have certified := Receipts.initialized_arm trace placeholders pre post receipt position
  exact ⟨certified.1,current_authenticated trace placeholders pre post (.armed receipt) index kind pid
    position (by intro wrong; cases wrong) (certified.2.symm.trans cause)⟩

theorem queue_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : TimerEffects.Queued Context)
    (index : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ .queued receipt :: post)
    (cause : receipt.cause = .ok (some ⟨index,.handshake kind pid⟩)) :
    receipt.Valid ∧ ∃ before rest, pre = before ++
      [.scope (.entered ⟨index,.handshake kind pid⟩),.old (.handshake (.callback kind pid))] ++ rest ∧
      HandshakeFresh.Available (before.filterMap handshake?) pid := by
  have certified := Receipts.initialized_queue trace placeholders pre post receipt position
  exact ⟨certified.1,current_authenticated trace placeholders pre post (.queued receipt) index kind pid
    position (by intro wrong; cases wrong) (certified.2.symm.trans cause)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
