import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedAccounting

/-! The inner result and byte-accounting continuation are one actual source
sequence. A stopped accounting frontier keeps the already settled canonical
ledger, the exact remaining send cursor and its physical cleanup debt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity StagedProvenance CompletionCuts

theorem focus_birth_free (encode : E → CausalJournal.Event) (decode : CausalJournal.Event → Option E)
    (quiet : ∀ event, birthPackets (encode event) = []) (action : PrefixM E α)
    (w : World) (history suffix : List CausalJournal.Event)
    (grown : (runPrefix (focusPrefix encode decode action) w history).2 = history ++ suffix) :
    ∀ event ∈ suffix, birthPackets event = [] := by
  change history ++ List.map encode _ = history ++ suffix at grown
  have same := List.append_cancel_left grown
  intro event member
  rw [← same] at member
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp member
  exact quiet e

theorem accounting_history_quiet (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) :
    HistoryFrame ledgerEvent?
      (FirstTerminal.focused (CompletionFirstTerminal.afterSocket pid packet ret)) := by
  have inner : HistoryFrame (fun e => ledgerEvent? (FirstTerminal.encode e))
      (CompletionFirstTerminal.afterSocket pid packet ret) := by
    unfold CompletionFirstTerminal.afterSocket
    apply HistoryFrame.bind (HistoryFrame.lift _ _)
    intro sent
    cases sent
    · exact HistoryFrame.pure _ _
    · apply HistoryFrame.bind
      · exact focusPrefix_other _ _ _ (fun _ => rfl) _
      · intro _; exact HistoryFrame.pure _ _
  intro w h
  obtain ⟨suffix,grown⟩ := CompletionFirstTerminal.afterSocket_appends pid packet ret w
    (h.filterMap CausalJournal.completion?)
  have empty : suffix.filterMap (fun e => ledgerEvent? (FirstTerminal.encode e)) = [] := by
    have same := inner w (h.filterMap CausalJournal.completion?)
    rw [grown,List.filterMap_append] at same
    have lengths := congrArg List.length same
    simp only [List.length_append] at lengths
    exact List.eq_nil_of_length_eq_zero (by omega)
  have focused := focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ w h
    (runPrefix (CompletionFirstTerminal.afterSocket pid packet ret) w
      (h.filterMap CausalJournal.completion?)).1 suffix (Prod.ext rfl grown)
  rw [focused]
  rw [List.filterMap_append,List.filterMap_map]
  change h.filterMap ledgerEvent? ++ suffix.filterMap (fun e => ledgerEvent? (FirstTerminal.encode e)) = _
  rw [empty,List.append_nil]

theorem indexed_accounting_checked (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (packet : RunWitness DataPacket) (ret : Int) :
    Ensures (fun h w => Owned context phase h ledger debts w)
      (IndexedStopped context ledger debts)
      (FirstTerminal.focused (CompletionFirstTerminal.afterSocket context.pid packet ret))
      (fun _ h w => Owned context phase h ledger debts w) := by
  apply indexed_passive_checked (.accounting context.pid packet ret) rfl (Appends.focus _ _ _)
    (accounting_history_quiet context.pid packet ret)
  · exact focus_birth_free _ _ completion_encode_births _
  · exact focusPrefix_erases _ _ (FirstTerminal.accounting_erases context.pid packet ret)
  · exact accounting_entry_view context.pid packet ret

/-- A later accounting Stop retains this same socket settlement and debt,
with an actual failed accounting run at the post-socket entry. -/
theorem indexed_inner_accounting
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (packetAt : PacketAt skb packet w)
    (peerValid : peer.Valid (liftWG (getPeer context.pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody context.pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle)) :
    let receipt : Completion.SocketReceipt := ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩
    let prior := history ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.socket prior.length (ret == 0)
    let journal := prior ++ [CausalJournal.Event.old (.socket receipt)]
    let actual := FirstTerminal.focused (Completion.socket context.pid skb packet peer ipv4 >>=
      CompletionFirstTerminal.afterSocket context.pid packet)
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      ∃ suffix, (runPrefix actual w history).2 = journal ++ suffix ∧
        match (runPrefix actual w history).1 with
        | .error reason => IndexedStopped context (settle [chosen.ticket] outcome ledger)
            (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts)
            reason (runPrefix actual w history).2
        | .ok (_,after) => Owned context (.sending rest) (runPrefix actual w history).2
            (settle [chosen.ticket] outcome ledger)
            (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) after := by
  dsimp only
  obtain ⟨chosen,member,head,socket,owned⟩ := indexed_inner_advanced before packetAt peerValid performed
  refine ⟨chosen,member,head,?_⟩
  rw [FirstTerminal.socket_accounting_factor,runPrefix_bind,socket]
  dsimp only
  obtain ⟨suffix,grown,result⟩ := indexed_accounting_checked context (.sending rest) _ _ packet ret v _ owned
  refine ⟨suffix,grown,?_⟩
  cases ended : (runPrefix (FirstTerminal.focused (CompletionFirstTerminal.afterSocket context.pid packet ret)) v
    ((history ++ middle.map FirstTerminal.encode) ++
      [CausalJournal.Event.old (.socket ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)])).1 with
  | error reason => simpa only [ended] using result
  | ok out => rcases out with ⟨sent,after⟩; simpa only [ended] using result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
