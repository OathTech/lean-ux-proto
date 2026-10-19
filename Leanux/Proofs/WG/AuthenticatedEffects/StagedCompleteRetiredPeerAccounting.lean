import Leanux.Proofs.WG.Queues.DurableHolders
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueues
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceQueueContents

/-! The missing upper half of peer-reference accounting uses the very same
physical RX carriers, durable holders and transient loans as C1's lower bound.
These local rules do not assert initialized preservation through every caller. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Queues.RxCredits
open Leanux.Proofs.WG.RetirementSecurity Leanux.Proofs.WG.TransmitSecurity

/-- No unexplained reference-count slack remains beyond the supplied actual
holder occurrences. Unlike Funded, this is an upper bound. -/
def Upper (holders : DurableHolders) (carriers : RxCredits.Ledger)
    (loans : Reservations) (w : WGWorld) : Prop :=
  ∀ owner, balance w owner ≤ demand carriers (holders.owners ++ loans) owner

variable {holders : DurableHolders} {carriers : RxCredits.Ledger}
  {loans before after : Reservations} {w v : WGWorld} {delta : HandoffDelta}
  {d : Device} {pid : PeerId} {p : Peer}

theorem Upper.initial (net bare : Bool) :
    Upper {} [] [] (Runner.initialWG net bare) := by
  intro owner
  cases net <;> cases bare <;>
    simp [balance,resident,Runner.initialWG]

/-- C1's native handoff equation is exact, so it also transports the upper
half on precisely the same holders, temporary loans and durable delta. -/
theorem Upper.handoff (upper : Upper holders carriers (loans ++ before) w)
    (step : Handoff w v before after delta) :
    Upper (holders.absorb delta) carriers (loans ++ after) v := by
  intro owner
  have old := upper owner
  have equation := step.count owner
  simp only [demand,List.count_append,DurableHolders.absorb_count] at *
  omega

theorem Upper.exact (upper : Upper holders carriers loans w)
    (funded : holders.Funded carriers loans w) (owner : Owner) :
    balance w owner = demand carriers (holders.owners ++ loans) owner :=
  Nat.le_antisymm (upper owner) (funded.carriers.funded owner)

/-- Empty native holder projections imply an empty durable account; funded
TX holders cannot hide behind an absent owner or a missing queue. -/
theorem holders_empty (funded : holders.Funded carriers loans w)
    (base : (w.dev.map Device.peerList).getD [] = [])
    (send : ∀ d, w.dev = some d → d.sendWorkQueue = [])
    (clear : (w.dev.map Device.clearWorkQueue).getD [] = [])
    (tx : txQueueContents w = fun _ => [])
    (cursor7 : DurableHolders.activeCursor w.nlSock7 = none)
    (cursor8 : DurableHolders.activeCursor w.nlSock8 = none) : holders.owners = [] := by
  have hb : holders.base = [] := by simpa [base] using funded.aligned.base
  have hc : holders.clear = [] := by simpa [clear] using funded.aligned.clear
  have h7 : holders.cursor7 = none := by simpa [cursor7] using funded.aligned.cursor7
  have h8 : holders.cursor8 = none := by simpa [cursor8] using funded.aligned.cursor8
  have hs : holders.send = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro owner member
    obtain ⟨peer,present⟩ := funded.resident (o := owner) (by
      simp [DurableHolders.owners,member])
    cases device : w.dev with
    | none => simp [resident,device] at present
    | some d =>
      have empty : holders.send.map Owner.slot = [] :=
        (funded.aligned.send d device).symm.trans (send d device)
      have mapped : owner.slot ∈ holders.send.map Owner.slot := List.mem_map.mpr ⟨owner,member,rfl⟩
      rw [empty] at mapped
      cases mapped
  have ht : holders.tx = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro item member
    obtain ⟨peer,present⟩ := funded.resident (o := item.owner) (by
      simp only [DurableHolders.owners,List.append_assoc,List.mem_append,List.mem_map]
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨item,member,rfl⟩))))
    cases device : w.dev with
    | none => simp [resident,device] at present
    | some d =>
      cases found : d.peers[item.owner.slot]? with
      | none => simp [resident,device,found] at present
      | some p =>
        have queues : handoffTxView w item.owner.slot = some p.txQueue.all := by
          simp [handoffTxView,device,found]
        have empty : p.txQueue.all = [] := by
          simpa [txQueueContents,queues] using congrFun tx item.owner.slot
        have alignment := funded.aligned.tx item.owner.slot p.txQueue.all queues
        have inside : item.item ∈ holders.items item.owner.slot := by
          simp only [DurableHolders.items,List.mem_map,List.mem_filter]
          exact ⟨item,⟨member,by simp⟩,rfl⟩
        rw [← alignment,empty] at inside
        cases inside
  simp [DurableHolders.owners,hb,hs,hc,ht,h7,h8]

/-- Once the actual account is empty, positivity rules out every resident
peer, including retired peers outside peerList. Both premises are explicit. -/
theorem peers_absent (upper : Upper holders [] [] w) (empty : holders.owners = [])
    (positive : ∀ (d : Device) (pid : PeerId) (p : Peer), w.dev = some d → d.peers[pid]? = some p → 0 < p.refcount)
    (device : w.dev = some d) (found : d.peers[pid]? = some p) : False := by
  have limit := upper ⟨d.ifindex,pid,p.internalId⟩
  have nonzero := positive d pid p device found
  simp [balance,resident,device,found,demand,charges,empty] at limit
  omega

theorem staged_empty (upper : Upper holders [] [] w) (empty : holders.owners = [])
    (positive : ∀ (d : Device) (pid : PeerId) (p : Peer), w.dev = some d → d.peers[pid]? = some p → 0 < p.refcount)
    (epoch : Nat) (pid : PeerId) (stamp : Nat) :
    Staged.Obligations.stagedPackets epoch pid stamp w = [] := by
  have missing : Staged.stagedAt w pid = none := by
    cases device : w.dev with
    | none => simp [Staged.stagedAt,device]
    | some d =>
      cases found : d.peers[pid]? with
      | none => simp [Staged.stagedAt,device,found]
      | some p => exact False.elim (peers_absent upper empty positive device found)
  simp [Staged.Obligations.stagedPackets,missing]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
