import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionSendCuts

/-! The native captured peer and family decisions lead to the same indexed
socket/accounting cut. Every successful inner result has one actual settlement;
a later accounting Stop keeps that successor ledger and its cleanup debt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionSendCuts

abbrev familyWorld (ipv4 : Bool) (w : World) : World :=
  if ipv4 then inet4World w else inet6World w

def SelectedFamily (ipv4 : Bool) (peer : RunWitness Peer) : Prop :=
  if ipv4 then (peer.value.endpoint.map (·.family)).getD 0 = AF_INET
  else (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET ∧
    (peer.value.endpoint.map (·.family)).getD 0 = AF_INET6

theorem family_send_run (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w u : World) (history : List CausalJournal.Event)
    (readEvents : List Completion.Event)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer) :
    runPrefix (FirstTerminal.focused (Completion.send pid skb packet)) w history =
      runPrefix (FirstTerminal.focused
        (Completion.socket pid skb packet peer ipv4 >>= CompletionFirstTerminal.afterSocket pid packet))
        (familyWorld ipv4 u) (history ++ readEvents.map FirstTerminal.encode) := by
  rw [focused_after_read pid skb packet peer w u history readEvents read]
  cases ipv4
  · exact focused_family6 pid skb packet peer u _ family.1 family.2
  · exact focused_family4 pid skb packet peer u _ family

/-- The actual read and family guards transport the incoming fixed ledger
into the inner socket, and any later accounting Stop retains its same first
terminal and cleanup debt. The successful socket premise is a local source
cut, not an assumption about the completed outer send. -/
theorem indexed_family_accounting
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
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
  have peerValid := (peer_cut_facts context.pid w u peer _ _ read).1
  rw [family_send_run context.pid skb packet peer ipv4 w u history readEvents read family]
  exact indexed_inner_accounting kept (packetAt.sameWG same) peerValid performed

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
