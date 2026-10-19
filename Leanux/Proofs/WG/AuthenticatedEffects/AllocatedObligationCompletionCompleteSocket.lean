import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteHistory

/-! Receipt completeness is paired with the exact same ledger successor
chosen by the actual inner socket cut, including errno. No independent
settlement witness or final enclosing return is used for this join. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete

theorem socket_cut
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
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      runPrefix (FirstTerminal.focused (Completion.socket context.pid skb packet peer ipv4)) w history =
        (.ok (ret,v),journal) ∧
      Owned context (.sending rest) journal (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) v ∧
      Complete journal (settle [chosen.ticket] outcome ledger) := by
  dsimp only
  obtain ⟨chosen,member,head,source,after⟩ := indexed_inner_advanced before packetAt peerValid performed
  refine ⟨chosen,member,head,source,after,?_⟩
  have quiet := completion_events_quiet
    (no_socket_suffix (socket_body_no_socket context.pid packet peer ipv4) performed)
  have prior := complete.append_quiet quiet
  have entry := before.append (middle.map FirstTerminal.encode) (by
    intro event inside
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp inside
    exact completion_encode_births original)
  have pending := (entry.cursor.assigned chosen member).1 (by simp [head])
  exact settle_singleton entry.entry prior pending rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
