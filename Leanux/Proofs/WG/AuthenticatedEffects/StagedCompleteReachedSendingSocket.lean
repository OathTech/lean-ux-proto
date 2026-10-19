import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingSource

/-! The fixed before-accounting prefix reaches the same inner socket receipt
and native world used to settle the head ticket. Captured peer access and family
choices are retained from the original callback entry, including ambient state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal Staged.Obligations StagedTerminalComplete

private theorem native_branch (w : World) (decision : Decision) (value : Bool) :
    (liftWG (branch decision value)).run w =
      .ok (value,{w with ambient := CounterWindow.record w.ambient decision value}) := rfl

theorem family_run (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w : World) (history : List Completion.Event)
    (family : SelectedFamily ipv4 peer) :
    runPrefix (familySocket pid skb packet peer) w history =
      runPrefix (Completion.socket pid skb packet peer ipv4) (familyWorld ipv4 w) history := by
  cases ipv4 with
  | false =>
    have is4 := beq_eq_false_iff_ne.mpr family.1
    have is6 : ((peer.value.endpoint.map (·.family)).getD 0 == AF_INET6) = true := by
      rw [family.2]; rfl
    simp [familySocket,is4,is6,runPrefix_bind,runPrefix_lift,native_branch,
      familyWorld,CompletionSendCuts.inet6World]
  | true =>
    have is4 : ((peer.value.endpoint.map (·.family)).getD 0 == AF_INET) = true := by
      rw [family]; rfl
    simp [familySocket,is4,runPrefix_bind,runPrefix_lift,native_branch,
      familyWorld,CompletionSendCuts.inet4World]

theorem prefix_after_read (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w u : World) (history : List CausalJournal.Event)
    (readEvents : List Completion.Event)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents)) :
    runPrefix (accountingPrefix pid skb packet) w history =
      runPrefix (FirstTerminal.focused (familySocket pid skb packet peer)) u
        (history ++ readEvents.map FirstTerminal.encode) := by
  have distribute := focusPrefix_bind_appends
    (a := captureObserved (Completion.access (getPeerMixed pid))) FirstTerminal.encode CausalJournal.completion?
    (by intro event; cases event <;> rfl)
    (Appends.captureObserved (Appends.focus _ _ _)) (family_appends pid skb packet) w history
  unfold accountingPrefix beforeAccounting
  rw [← distribute,runPrefix_bind,
    focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ w history (.ok (peer,u)) readEvents read]

theorem prefix_family (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w u : World) (history : List CausalJournal.Event)
    (readEvents : List Completion.Event)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer) :
    runPrefix (accountingPrefix pid skb packet) w history =
      runPrefix (FirstTerminal.focused (Completion.socket pid skb packet peer ipv4))
        (familyWorld ipv4 u) (history ++ readEvents.map FirstTerminal.encode) := by
  rw [prefix_after_read pid skb packet peer w u history readEvents read]
  change ((runPrefix (familySocket pid skb packet peer) u _).1,
    _ ++ List.map FirstTerminal.encode _) = _
  rw [family_run pid skb packet peer ipv4 u _ family]
  rfl

theorem socket_prefix
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (complete : Complete history ledger) (packetAt : PacketAt skb packet w) (ipv4 : Bool)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ readEvents))
    (family : SelectedFamily ipv4 peer)
    (performed : runPrefix (socketBody context.pid packet peer ipv4) (familyWorld ipv4 u)
      ((history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?) =
        (.ok (ret,v),(history ++ readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion? ++ middle)) :
    let prior := (history ++ readEvents.map FirstTerminal.encode) ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.socket prior.length (ret == 0)
    let receipt : Completion.SocketReceipt := ⟨context.pid,skb,packet,peer,ipv4,⟨ret,familyWorld ipv4 u,v⟩⟩
    let journal := prior ++ [CausalJournal.Event.old (.socket receipt)]
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      runPrefix (accountingPrefix context.pid skb packet) w history = (.ok (ret,v),journal) ∧
      Owned context (.sending rest) journal (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) v ∧
      Complete journal (settle [chosen.ticket] outcome ledger) := by
  dsimp only
  have readWorld := FirstTerminal.peer_cut_world context.pid w u peer _ _ read
  have same : (familyWorld ipv4 u).wg = w.wg := by cases ipv4 <;> exact readWorld
  have kept := (before.append (readEvents.map FirstTerminal.encode) (by
    intro event member
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp member
    exact completion_encode_births e)).sameWG same
  have paired := Converse.extension complete rfl
    (mapped_quiet_suffix (read_ledger_quiet context.pid) w history readEvents (congrArg Prod.snd read))
  have peerValid := (peer_cut_facts context.pid w u peer _ _ read).1
  obtain ⟨chosen,member,head,socket,owned,after⟩ :=
    Converse.socket_cut kept paired (packetAt.sameWG same) peerValid performed
  exact ⟨chosen,member,head,(prefix_family context.pid skb packet peer ipv4 w u history readEvents read family).trans socket,owned,after⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
