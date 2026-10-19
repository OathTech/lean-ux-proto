import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionCapture

/-! The real inner socket event crosses from the pending ledger to its one
chosen terminal ledger. Every later accounting prefix uses that same ledger,
even when the accounting continuation stops before the outer result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {Safe : List CausalJournal.Event → Prop} {packet : RunWitness DataPacket}

theorem socket_cuts (accountSafe : AccountSafe Safe)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w)
    (peerValid : peer.Valid (liftWG (getPeer context.pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody context.pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle)) :
    let receipt : TransmitSecurity.Completion.SocketReceipt := ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩
    let prior := history ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.socket prior.length (ret == 0)
    let journal := prior ++ [CausalJournal.Event.old (.socket receipt)]
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      runPrefix (FirstTerminal.focused (TransmitSecurity.Completion.socket context.pid skb packet peer ipv4)) w history =
        (.ok (ret,v),journal) ∧
      Owned context (.sending rest) journal (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) v ∧
      Complete journal (settle [chosen.ticket] outcome ledger) ∧
      Cuts Safe history (middle.map FirstTerminal.encode ++ [CausalJournal.Event.old (.socket receipt)]) := by
  dsimp only
  obtain ⟨chosen,member,head,source,owned,settled⟩ := Converse.socket_cut before complete packetAt peerValid performed
  have quiet := mapped_quiet_suffix (socket_body_ledger_quiet context.pid packet peer ipv4)
    w history middle (congrArg Prod.snd performed)
  have prior := quiet_cuts accountSafe before complete quiet
  exact ⟨chosen,member,head,source,owned,settled,
    prior.append (Cuts.singleton prior.last (owned_safe accountSafe owned settled))⟩

theorem accounting (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) (packet : RunWitness DataPacket) (ret : Int)
    (accountSafe : AccountSafe Safe) :
    Checked (fun h w => Owned context phase h ledger debts w ∧ Complete h ledger) Safe
      (fun reason h => IndexedStopped context ledger debts reason h ∧ Complete h ledger)
      (FirstTerminal.focused (CompletionFirstTerminal.afterSocket context.pid packet ret))
      (fun _ h w => Owned context phase h ledger debts w ∧ Complete h ledger) := by
  have appends : Appends (FirstTerminal.focused (CompletionFirstTerminal.afterSocket context.pid packet ret)) :=
    Appends.focus _ _ _
  have quiet := accounting_history_quiet context.pid packet ret
  apply Checked.of_cuts
  · intro w h before
    obtain ⟨suffix,grown,result⟩ := indexed_accounting_checked context phase ledger debts packet ret w h before.1
    have paired := Converse.history_preserved before.2 appends quiet (w := w)
    refine ⟨suffix,grown,?_⟩
    cases run : (runPrefix (FirstTerminal.focused (CompletionFirstTerminal.afterSocket context.pid packet ret)) w h).1 with
    | error reason => exact ⟨by simpa only [run] using result,paired⟩
    | ok out => exact ⟨by simpa only [run] using result,paired⟩
  · intro w h before
    exact quiet_output accountSafe before.1 before.2 appends quiet

theorem inner_accounting_cuts (accountSafe : AccountSafe Safe)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w)
    (peerValid : peer.Valid (liftWG (getPeer context.pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody context.pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle)) :
    let prior := history ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.socket prior.length (ret == 0)
    let actual := FirstTerminal.focused (TransmitSecurity.Completion.socket context.pid skb packet peer ipv4 >>=
      CompletionFirstTerminal.afterSocket context.pid packet)
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      Complete (runPrefix actual w history).2 (settle [chosen.ticket] outcome ledger) ∧
      ∃ suffix, (runPrefix actual w history).2 = history ++ suffix ∧ Cuts Safe history suffix ∧
        match (runPrefix actual w history).1 with
        | .error reason => IndexedStopped context (settle [chosen.ticket] outcome ledger)
            (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) reason (runPrefix actual w history).2
        | .ok (_,after) => Owned context (.sending rest) (runPrefix actual w history).2
            (settle [chosen.ticket] outcome ledger)
            (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) after := by
  dsimp only
  obtain ⟨chosen,member,head,socket,owned,settled,cuts⟩ := socket_cuts accountSafe before complete packetAt peerValid performed
  refine ⟨chosen,member,head,?_⟩
  rw [FirstTerminal.socket_accounting_factor,runPrefix_bind,socket]
  dsimp only
  have quiet := accounting_history_quiet context.pid packet ret
  have paired := Converse.history_preserved settled (Appends.focus _ _ _) quiet (w := v)
  obtain ⟨suffix,grown,result⟩ := indexed_accounting_checked context (.sending rest) _ _ packet ret v _ owned
  have tailCuts := quiet_cuts accountSafe owned settled (grown ▸ quiet v _)
  refine ⟨paired,(middle.map FirstTerminal.encode ++ [CausalJournal.Event.old (.socket ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)]) ++ suffix,?_,?_,?_⟩
  · simpa only [List.append_assoc] using grown
  · exact cuts.append (by simpa only [List.append_assoc] using tailCuts)
  · cases ended : (runPrefix (FirstTerminal.focused (CompletionFirstTerminal.afterSocket context.pid packet ret)) v
        ((history ++ middle.map FirstTerminal.encode) ++
          [CausalJournal.Event.old (.socket ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)])).1 with
    | error reason => simpa only [ended] using result
    | ok out => rcases out with ⟨sent,after⟩; simpa only [ended] using result

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
