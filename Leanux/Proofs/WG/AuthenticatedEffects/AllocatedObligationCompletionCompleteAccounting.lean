import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSocket

/-! A successful native socket result has already consumed its one ticket.
The later accounting prefix preserves completeness on that exact successor,
including an accounting Stop after the first terminal has been recorded. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete

theorem inner_accounting
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger)
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
      Complete (runPrefix actual w history).2 (settle [chosen.ticket] outcome ledger) ∧
      ∃ suffix, (runPrefix actual w history).2 = journal ++ suffix ∧
        match (runPrefix actual w history).1 with
        | .error reason => IndexedStopped context (settle [chosen.ticket] outcome ledger)
            (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts)
            reason (runPrefix actual w history).2
        | .ok (_,after) => Owned context (.sending rest) (runPrefix actual w history).2
            (settle [chosen.ticket] outcome ledger)
            (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) after := by
  dsimp only
  obtain ⟨chosen,member,head,socket,owned,settled⟩ := socket_cut before complete packetAt peerValid performed
  refine ⟨chosen,member,head,?_⟩
  rw [FirstTerminal.socket_accounting_factor,runPrefix_bind,socket]
  dsimp only
  refine ⟨history_preserved settled (Appends.focus _ _ _)
    (accounting_history_quiet context.pid packet ret),?_⟩
  obtain ⟨suffix,grown,result⟩ := indexed_accounting_checked context (.sending rest) _ _ packet ret v _ owned
  refine ⟨suffix,grown,?_⟩
  cases ended : (runPrefix (FirstTerminal.focused (CompletionFirstTerminal.afterSocket context.pid packet ret)) v
    ((history ++ middle.map FirstTerminal.encode) ++
      [CausalJournal.Event.old (.socket ⟨context.pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)])).1 with
  | error reason => simpa only [ended] using result
  | ok out => rcases out with ⟨sent,after⟩; simpa only [ended] using result

theorem family_accounting
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger)
    (packetAt : PacketAt skb packet w) (ipv4 : Bool)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (performed : runPrefix (CompletionFirstTerminal.socketBody context.pid packet peer ipv4)
      (familyWorld ipv4 u)
      ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
        (.ok (ret,v),(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ middle)) :
    let prior := (history ++ readEvents.map FirstTerminal.encode) ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.socket prior.length (ret == 0)
    let receipt : Completion.SocketReceipt := ⟨context.pid,skb,packet,peer,ipv4,⟨ret,familyWorld ipv4 u,v⟩⟩
    let journal := prior ++ [CausalJournal.Event.old (.socket receipt)]
    let actual := FirstTerminal.focused (Completion.send context.pid skb packet)
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      Complete (runPrefix actual w history).2 (settle [chosen.ticket] outcome ledger) ∧
      ∃ suffix, (runPrefix actual w history).2 = journal ++ suffix ∧
        match (runPrefix actual w history).1 with
        | .error reason => IndexedStopped context (settle [chosen.ticket] outcome ledger)
            (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts)
            reason (runPrefix actual w history).2
        | .ok (_,after) => Owned context (.sending rest) (runPrefix actual w history).2
            (settle [chosen.ticket] outcome ledger)
            (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) after := by
  dsimp only
  have readWorld := FirstTerminal.peer_cut_world context.pid w u peer _ _ read
  have same : (familyWorld ipv4 u).wg = w.wg := by
    cases ipv4 <;> exact readWorld
  have kept := (before.append (readEvents.map FirstTerminal.encode) (by
    intro event member
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp member
    exact completion_encode_births e)).sameWG same
  have prior := extension complete rfl
    (mapped_quiet_suffix (read_ledger_quiet context.pid) w history readEvents (congrArg Prod.snd read))
  have peerValid := (peer_cut_facts context.pid w u peer _ _ read).1
  rw [family_send_run context.pid skb packet peer ipv4 w u history readEvents read family]
  exact inner_accounting kept prior (packetAt.sameWG same) peerValid performed

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
