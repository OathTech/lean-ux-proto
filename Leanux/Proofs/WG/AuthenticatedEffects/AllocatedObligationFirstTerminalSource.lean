import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalSettlement
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionFirstTerminalSource

/-! These are the actual completion-source cuts, before accounting or later
free. Prefix extension is taken from the same execution, including any earlier
observer events; native erasure is used only to certify the captured run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

abbrev encode : Completion.Event → CausalJournal.Event := CausalJournal.Event.old ∘ Journal.completionEvent

abbrev focused (body : PrefixM Completion.Event α) : PrefixM CausalJournal.Event α :=
  focusPrefix encode CausalJournal.completion? body

/-- Every normal inner socket result is recorded before later accounting,
including errno. Its concrete native receipt and exact final-journal position
come from the same focused observer run. -/
theorem inner_cut (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w v : World)
    (history : List CausalJournal.Event) (middle : List Completion.Event) (ret : Int)
    (packetValid : packet.Valid (liftWG (getTxSkb skb)))
    (peerValid : peer.Valid (liftWG (getPeer pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle)) :
    let receipt : Completion.SocketReceipt := ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩
    receipt.Valid ∧
      runPrefix (focused (Completion.socket pid skb packet peer ipv4)) w history =
        (.ok (ret,v),(history ++ middle.map encode) ++ [.old (.socket receipt)]) := by
  dsimp only
  have nativeRun := CompletionFirstTerminal.socket_result pid skb packet peer ipv4 w v
    (history.filterMap CausalJournal.completion?) _ ret performed
  refine ⟨⟨packetValid,peerValid,?_⟩,?_⟩
  · exact (Completion.socket_erases pid skb packet peer ipv4 w
      (history.filterMap CausalJournal.completion?)).symm.trans (congrArg Prod.fst nativeRun)
  · have projected := focusPrefix_suffix encode CausalJournal.completion?
      (Completion.socket pid skb packet peer ipv4) w history (.ok (ret,v))
      (middle ++ [.socket ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩])
      (by simpa only [List.append_assoc] using nativeRun)
    simpa only [focused,List.map_append,List.map_cons,List.map_nil,
      List.append_assoc,encode,Function.comp_apply,Journal.completionEvent] using projected

/-- The exact source inner result supplies the first-terminal settlement.
A successful or failed socket still leaves the cell for the later cleanup cut. -/
theorem inner_settlement (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w v : World)
    (history : List CausalJournal.Event) (middle : List Completion.Event) (ret : Int)
    (packetValid : packet.Valid (liftWG (getTxSkb skb)))
    (peerValid : peer.Valid (liftWG (getPeer pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle))
    (valid : Valid births ledger) (resident : Resident history ledger w.wg)
    (injective : Injective history ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let receipt : Completion.SocketReceipt := ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩
    let before := history ++ middle.map encode
    let outcome := Staged.Obligations.Terminal.socket before.length (ret == 0)
    let after := settle [ticket] outcome ledger
    let journal := before ++ [CausalJournal.Event.old (.socket receipt)]
    runPrefix (focused (Completion.socket pid skb packet peer ipv4)) w history =
      (.ok (ret,v),journal) ∧
      Staged.Obligations.Step ledger after ∧ Valid births after ∧
      Resident journal after v.wg ∧ Injective journal after ∧
      (ticket,Status.terminal outcome) ∈ after ∧
      PacketMaterial.view v.wg skb = some value := by
  dsimp only
  obtain ⟨native,observed⟩ := inner_cut pid skb packet peer ipv4 w v history middle ret
    packetValid peerValid performed
  have settled := socket _ native valid (resident.append _) (injective.append resident _)
    pending (origin.append (middle.map encode))
  exact ⟨observed,settled.1,settled.2.1,settled.2.2.1,settled.2.2.2.1,
    settled.2.2.2.2.1,settled.2.2.2.2.2.2.2.1⟩

/-- The first inner result survives every append-only continuation, including
a stopped one. This covers errno as well as success and does not rely on a
completed outer send or completed packet cleanup. -/
theorem inner_retained (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w v : World)
    (history : List CausalJournal.Event) (middle : List Completion.Event) (ret : Int)
    (packetValid : packet.Valid (liftWG (getTxSkb skb)))
    (peerValid : peer.Valid (liftWG (getPeer pid)))
    (performed : runPrefix (CompletionFirstTerminal.socketBody pid packet peer ipv4) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (ret,v),history.filterMap CausalJournal.completion? ++ middle))
    (next : Int → PrefixM CausalJournal.Event α) (appends : ∀ value, Appends (next value)) :
    ∃ suffix, (runPrefix (focused (Completion.socket pid skb packet peer ipv4) >>= next)
      w history).2 = (history ++ middle.map encode) ++
        CausalJournal.Event.old (.socket ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩) :: suffix := by
  obtain ⟨_,observed⟩ := inner_cut pid skb packet peer ipv4 w v history middle ret
    packetValid peerValid performed
  obtain ⟨suffix,grown⟩ := appends ret v ((history ++ middle.map encode) ++
    [CausalJournal.Event.old (.socket ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩)])
  refine ⟨suffix,?_⟩
  rw [runPrefix_bind,observed]
  simpa only [List.append_assoc,List.singleton_append] using grown

private theorem peer_world (pid : PeerId) : SameView World.wg (liftWG (getPeer pid)) := by
  apply sameView_liftWG World.wg id (getPeer pid)
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact (Peers.getPeer_current pid w v p a b run).1
  · intro w g a same
    exact same

/-- Capturing the native peer lookup changes no WG state. This discharges the
unsupported-family path's physical frame at its actual source read. -/
theorem peer_cut_world (pid : PeerId) (w u : World) (peer : RunWitness Peer)
    (history middle : List Completion.Event)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w history =
      (.ok (peer,u),middle)) : u.wg = w.wg := by
  rw [runPrefix_captureObserved] at read
  cases result : runPrefix (Completion.access (getPeerMixed pid)) w history with
  | mk out events =>
    rw [result] at read
    cases out with
    | error stop => cases read
    | ok out =>
      rcases out with ⟨value,v⟩
      simp only [Except.map,Prod.mk.injEq,Except.ok.injEq] at read
      have same : v = u := read.1.2
      have native := (Completion.access_erases (getPeerMixed_erases pid) w history).symm.trans
        (congrArg Prod.fst result)
      exact same ▸ (ProjectedAction.iff_run _ _ _).mp (peer_world pid) w value v native

/-- An unsupported-family result records a counterless refusal only after an
actual no-inner-socket suffix; it cannot reclassify an inner socket errno. -/
theorem unsupported_cut (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w u : World) (history : List CausalJournal.Event)
    (middle : List Completion.Event)
    (packetValid : packet.Valid (liftWG (getTxSkb skb)))
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ middle))
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6) :
    let v := CompletionFirstTerminal.refusedWorld u
    let receipt : SendResult.Receipt := ⟨pid,skb,packet,⟨false,w,v⟩⟩
    receipt.Valid ∧ v.wg = w.wg ∧ middle.filterMap Completion.socket? = [] ∧
      runPrefix (SendResult.observed CausalJournal.Event.sendResult
        (focused (Completion.send pid skb packet)) pid skb packet) w history =
        (.ok (false,v),(history ++ middle.map encode) ++ [.sendResult receipt]) := by
  dsimp only
  have cut := CompletionFirstTerminal.unsupported_observed encode CausalJournal.completion?
    CausalJournal.Event.sendResult pid skb packet peer w u history middle read not4 not6
  have nativeRun := CompletionFirstTerminal.send_unsupported pid skb packet peer w u _ _ read not4 not6
  refine ⟨⟨packetValid,?_⟩,peer_cut_world pid w u peer _ _ read,cut.1,cut.2⟩
  exact (Completion.send_erases pid skb packet w
    (history.filterMap CausalJournal.completion?)).symm.trans (congrArg Prod.fst nativeRun)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
