import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedCapture

/-! The original unsupported-family result is a first terminal only on the
actual no-socket branch. Its captured peer read derives the current source
entry, and the same selected ticket becomes indexed cleanup debt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity StagedProvenance HandshakeSecurity.StagedConservation

theorem peer_cut_facts (pid : PeerId) (w u : World) (peer : RunWitness Peer)
    (history middle : List Completion.Event)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w history =
      (.ok (peer,u),middle)) : peer.Valid (liftWG (getPeer pid)) ∧ peer.before = w := by
  rw [runPrefix_captureObserved] at read
  cases result : runPrefix (Completion.access (getPeerMixed pid)) w history with
  | mk out events =>
    rw [result] at read
    cases out with
    | error stop => cases read
    | ok out =>
      obtain ⟨value,v⟩ := out
      simp only [Except.map,Prod.mk.injEq,Except.ok.injEq] at read
      have captured : (⟨value,w,v⟩ : RunWitness Peer) = peer := read.1.1
      rw [← captured]
      exact ⟨(Completion.access_erases (getPeerMixed_erases pid) w history).symm.trans
        (congrArg Prod.fst result),rfl⟩

/-- The exact unsupported-family arm has no earlier inner socket in this
send. It settles the current allocated head to its named uncounted refusal. -/
theorem indexed_unsupported_advanced
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (packetAt : PacketAt skb packet w)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ middle))
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6) :
    let v := CompletionFirstTerminal.refusedWorld u
    let receipt : SendResult.Receipt := ⟨context.pid,skb,packet,⟨false,w,v⟩⟩
    let prior := history ++ middle.map FirstTerminal.encode
    let outcome := Staged.Obligations.Terminal.sendRefused prior.length
    let journal := prior ++ [CausalJournal.Event.sendResult receipt]
    ∃ chosen : Binding, chosen ∈ context.bindings ∧ chosen.skb = skb ∧
      middle.filterMap Completion.socket? = [] ∧
      runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history =
        (.ok (false,v),journal) ∧
      Owned context (.sending rest) journal (settle [chosen.ticket] outcome ledger)
        (⟨chosen.ticket,chosen.position,chosen.ordinal,outcome⟩ :: debts) v := by
  dsimp only
  obtain ⟨native,world,noSocket,observed⟩ := FirstTerminal.unsupported_cut context.pid skb packet peer w u
    history middle packetAt.1 read not4 not6
  obtain ⟨peerValid,peerEntry⟩ := peer_cut_facts context.pid w u peer _ _ read
  have member : skb ∈ context.items := by
    obtain ⟨left,equal⟩ := before.cursor.remaining
    rw [← equal]
    simp [Phase.remaining]
  obtain ⟨chosen,inside,head⟩ := List.mem_map.mp member
  have kept := before.append (middle.map FirstTerminal.encode) (by
    intro event member
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp member
    exact completion_encode_births e)
  have pending := (kept.cursor.assigned chosen inside).1 (by simp [head])
  have origin : Origin (history ++ middle.map FirstTerminal.encode) chosen.position chosen.ordinal
      chosen.generation skb chosen.value := by
    simpa only [Binding.recorded,head] using kept.cursor.recorded chosen inside
  have backed := kept.entry.core.physical.resident chosen.ticket chosen.position chosen.ordinal pending
  have atRead : Backed (history ++ middle.map FirstTerminal.encode) chosen.position chosen.ordinal packet.before.wg := by
    rw [packetAt.before_current]
    exact backed
  have evidence : At (history ++ middle.map FirstTerminal.encode)
      (CausalJournal.Event.sendResult ⟨context.pid,skb,packet,⟨false,w,CompletionFirstTerminal.refusedWorld u⟩⟩)
      chosen.ticket (.sendRefused (history ++ middle.map FirstTerminal.encode).length) :=
    .refused _ native rfl peer peerValid peerEntry not4 not6
      chosen.position chosen.ordinal chosen.generation chosen.value
      ((kept.entry.allocationLinks chosen.ticket chosen.position chosen.ordinal pending).at_origin origin) atRead
  exact ⟨chosen,inside,head,noSocket,observed,(kept.sameWG world).settle_head chosen inside head evidence rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
