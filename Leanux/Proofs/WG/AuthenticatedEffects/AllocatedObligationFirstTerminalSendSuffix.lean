import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalAccounting

/-! The selected-family suffix is the actual inner socket followed by native
byte accounting. This composition keeps its first terminal and physical debt;
batch iteration, timer callbacks and global entry transport remain separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

private theorem socket_appends (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : Appends (Completion.socket pid skb packet peer ipv4) := by
  unfold Completion.socket
  apply Appends.receiptObserved
  cases ipv4 <;> exact Appends.focus _ _ _

theorem socket_accounting_factor (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w : World) (history : List CausalJournal.Event) :
    runPrefix (focused (Completion.socket pid skb packet peer ipv4 >>=
      CompletionFirstTerminal.afterSocket pid packet)) w history =
    runPrefix (focused (Completion.socket pid skb packet peer ipv4) >>=
      fun ret => focused (CompletionFirstTerminal.afterSocket pid packet ret)) w history :=
  (focusPrefix_bind_appends encode CausalJournal.completion? (by intro event; cases event <;> rfl)
    (socket_appends pid skb packet peer ipv4) (CompletionFirstTerminal.afterSocket_appends pid packet)
    w history).symm

/-- The native socket/accounting sequence keeps exactly the first socket
outcome and leaves its chosen allocation as cleanup debt. A normal outer false
after errno does not become a new refusal or replace that outcome. -/
theorem inner_accounted (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w v u : World)
    (history suffix : List CausalJournal.Event) (middle : List Completion.Event)
    (ret : Int) (sent : Bool)
    (packetValid : packet.Valid (liftWG (getTxSkb skb)))
    (peerValid : peer.Valid (liftWG (getPeer pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle))
    (accounted : runPrefix (focused (CompletionFirstTerminal.afterSocket pid packet ret)) v
      ((history ++ middle.map encode) ++
        [.old (.socket ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)]) =
      (.ok (sent,u),((history ++ middle.map encode) ++
        [.old (.socket ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)]) ++ suffix))
    (support : Support births history ledger debts w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let receipt : Completion.SocketReceipt := ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩
    let outcome := Staged.Obligations.Terminal.socket (history ++ middle.map encode).length (ret == 0)
    let after := settle [ticket] outcome ledger
    let debt : CleanupDebt := ⟨ticket,position,ordinal,outcome⟩
    let journal := ((history ++ middle.map encode) ++ [CausalJournal.Event.old (.socket receipt)]) ++ suffix
    runPrefix (focused (Completion.socket pid skb packet peer ipv4 >>=
      CompletionFirstTerminal.afterSocket pid packet)) w history = (.ok (sent,u),journal) ∧
      Staged.Obligations.Step ledger after ∧ Support births journal after (debt :: debts) u.wg ∧
      (ticket,Status.terminal outcome) ∈ after := by
  dsimp only
  obtain ⟨observed,step,atSocket,terminal,_⟩ := inner_debt pid skb packet peer ipv4 w v
    history middle ret packetValid peerValid performed support pending origin
  refine ⟨?_,step,accounting_support pid packet ret v u _ suffix sent accounted atSocket,terminal⟩
  rw [socket_accounting_factor,runPrefix_bind,observed]
  exact accounted

/-- The actual selected-family suffix retains the inner socket occurrence
even when byte accounting Stops. This is an occurrence claim at the reached
cut; it does not invent a successful final world for a stopped execution. -/
theorem inner_accounting_retained (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w v : World)
    (history : List CausalJournal.Event) (middle : List Completion.Event) (ret : Int)
    (packetValid : packet.Valid (liftWG (getTxSkb skb)))
    (peerValid : peer.Valid (liftWG (getPeer pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle)) :
    ∃ suffix, (runPrefix (focused (Completion.socket pid skb packet peer ipv4 >>=
      CompletionFirstTerminal.afterSocket pid packet)) w history).2 =
      (history ++ middle.map encode) ++
        CausalJournal.Event.old (.socket ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩) :: suffix := by
  rw [socket_accounting_factor]
  exact inner_retained pid skb packet peer ipv4 w v history middle ret packetValid peerValid
    performed (fun value => focused (CompletionFirstTerminal.afterSocket pid packet value))
    (fun _ => Appends.focus _ _ _)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
