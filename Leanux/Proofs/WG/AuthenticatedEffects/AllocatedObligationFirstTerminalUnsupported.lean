import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalSource

/-! The unsupported-address arm is an uncounted terminal outcome only when
the original source read rules out both socket branches. A false outer result
alone is insufficient, because an inner errno has already settled its ticket. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

/-- An actual unsupported-family send settles the pending allocation once,
without an inner socket event or a counted drop. Its cell remains resident for
the real disposal continuation. All entry backing assumptions stay explicit. -/
theorem unsupported_settlement (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w u : World) (history : List CausalJournal.Event)
    (middle : List Completion.Event)
    (packetValid : packet.Valid (liftWG (getTxSkb skb)))
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap CausalJournal.completion?) =
        (.ok (peer,u),history.filterMap CausalJournal.completion? ++ middle))
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6)
    (valid : Valid births ledger) (resident : Resident history ledger w.wg)
    (injective : Injective history ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let v := CompletionFirstTerminal.refusedWorld u
    let receipt : SendResult.Receipt := ⟨pid,skb,packet,⟨false,w,v⟩⟩
    let before := history ++ middle.map encode
    let outcome := Staged.Obligations.Terminal.sendRefused before.length
    let after := settle [ticket] outcome ledger
    let journal := before ++ [CausalJournal.Event.sendResult receipt]
    middle.filterMap Completion.socket? = [] ∧
      runPrefix (SendResult.observed CausalJournal.Event.sendResult
        (focused (Completion.send pid skb packet)) pid skb packet) w history =
        (.ok (false,v),journal) ∧
      Staged.Obligations.Step ledger after ∧ Valid births after ∧
      Resident journal after v.wg ∧ Injective journal after ∧
      (ticket,Status.terminal outcome) ∈ after ∧
      PacketMaterial.view v.wg skb = some value ∧
      (∀ other previous, (other,Status.terminal previous) ∈ ledger →
        (other,Status.terminal previous) ∈ after) := by
  dsimp only
  obtain ⟨_,world,noSocket,observed⟩ := unsupported_cut pid skb packet peer w u history middle
    packetValid read not4 not6
  let outcome := Staged.Obligations.Terminal.sendRefused (history ++ middle.map encode).length
  have selected : ∀ t ∈ [ticket], t ∈ pendingAt (.allocated position ordinal) ledger := by
    intro t member
    have same : t = ticket := by simpa using member
    subst t
    exact mem_pendingAt.mpr pending
  have step := settle_pending (valid.1.symm ▸ valid.2) selected (outcome := outcome)
  have kept : Resident history (settle [ticket] outcome ledger) w.wg :=
    fun other batch index member => resident other batch index
      (pending_after_settle [ticket] outcome member).1
  have atEnd : Resident history (settle [ticket] outcome ledger)
      (CompletionFirstTerminal.refusedWorld u).wg := by rw [world]; exact kept
  have cell := (resident ticket position ordinal pending).at_origin origin
  refine ⟨noSocket,observed,step,step.valid valid,(atEnd.append _).append _,
    ((injective.settle [ticket] outcome).append atEnd _).append (atEnd.append _) _,?_,
    (by rw [world]; exact cell.2),fun _ _ prior => step.terminal prior⟩
  apply List.mem_map.mpr
  exact ⟨(ticket,Status.pending (.allocated position ordinal)),pending,by simp⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
