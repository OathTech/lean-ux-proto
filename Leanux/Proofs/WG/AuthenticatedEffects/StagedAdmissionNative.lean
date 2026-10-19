import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionQueues
import Leanux.Proofs.WG.TransmitSecurity.StagedKeepalive

/-! Fixed-ledger admission at connected native routing and keepalive cuts.
The incoming ledger, history bound and exact queue carrier remain explicit.
Routing uses the actual splice entry after trimming; this file neither omits
nor repeats the earlier counted disposal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal
set_option pp.structureInstances false

/-- The actual routing prefix and final splice admit precisely the packets
in this receipt, at its journal position and packet ordinals. Existing terminal
outcomes survive; the caller supplies the carrier at the actual splice entry. -/
theorem routed (r : Journal.RoutingHistory.Receipt) (pid : PeerId)
    (selected : r.run.value = .ok pid)
    (u q w : WGWorld) (a b c : Ambient)
    (check : ((Packets.txCheck r.family r.addr r.packets r.mtu).run r.run.before).run r.run.ambientBefore = .ok ((true,u),a))
    (lookup : ((lookupDst r.family r.addr).run u).run a = .ok ((some pid,q),b))
    (select : ((Packets.txSelect r.family r.packets r.mtu (some pid)).run q).run b =
      .ok ((.ok (pid,r.packets.map (fun p => {p with mtu := r.mtu})),w),c))
    (spliceRun : ((Lifetimes.xmitSplice pid (r.packets.map (fun p => {p with mtu := r.mtu}))).run w).run c =
      .ok (((),r.run.after),r.run.ambientAfter))
    (validBefore : Valid births ledger) (bounded : Bounded history.length births)
    (before : QueueInv history ledger w) :
    ∃ generation stamp,
      let added := r.packets.map (fun p => {p with mtu := r.mtu})
      let event := Event.old (.routed r.family r.addr r.packets r.mtu r.run)
      let next := appendBirths ledger history.length (.staged generation pid stamp) added
      Valid (births ++ freshTickets history.length 0 added) next ∧
        Bounded (history ++ [event]).length (births ++ freshTickets history.length 0 added) ∧
        QueueInv (history ++ [event]) next r.run.after ∧
        (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
          (ticket,Status.terminal outcome) ∈ next) ∧
        Staged.dropped r.run.after = Staged.dropped w := by
  have run : r.Valid := by
    change ((Packets.txFront r.family r.addr r.packets r.mtu).run r.run.before).run r.run.ambientBefore = _
    rw [selected]
    exact Packets.TxFrontCut.run ⟨u,q,w,a,b,c,check,lookup,select,spliceRun⟩
  let added := r.packets.map (fun p => {p with mtu := r.mtu})
  let cut : WGRunWitness Unit := ⟨(),w,r.run.after,c,r.run.ambientAfter⟩
  obtain ⟨d,p,device,resident,changed,charge⟩ := Staged.splice pid added cut spliceRun
  dsimp only [cut] at device changed charge
  have epoch : Packets.epoch w = some d.ifindex := by simp [Packets.epoch,device]
  have sameEpoch : Packets.epoch r.run.after = Packets.epoch w := by
    simp only [Packets.epoch,changed,device,Option.map_some]
  have old : Staged.stagedAt w pid = some (p.internalId,p.staged) := by
    simp [Staged.stagedAt,device,resident]
  have after : Staged.stagedAt r.run.after pid = some (p.internalId,p.staged ++ added) := by
    simp [Staged.stagedAt,changed]
  have others : ∀ other, pid ≠ other → Staged.stagedAt r.run.after other = Staged.stagedAt w other := by
    intro other different
    simp [Staged.stagedAt,changed,device,Std.TreeMap.getElem?_insert,different]
  have born := routed_births r run selected (sameEpoch.trans epoch) after history
  obtain ⟨validNext,boundNext,queueNext,terminals⟩ :=
    admission validBefore bounded before epoch sameEpoch old after others born
  exact ⟨d.ifindex,p.internalId,validNext,boundNext,queueNext,terminals,charge⟩

/-- Native keepalive preparation admits one ticket only at the successful
empty-queue allocation arm. A nonempty queue or refused allocation adds none. -/
theorem keepalive (pid : PeerId) (r : WGRunWitness Bool)
    (run : r.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
    (validBefore : Valid births ledger) (bounded : Bounded history.length births)
    (before : QueueInv history ledger r.before) :
    (r.after = r.before ∧ Valid births ledger ∧
      Bounded (history ++ [Event.keepalivePrepared pid r]).length births ∧
      QueueInv (history ++ [Event.keepalivePrepared pid r]) ledger r.after) ∨
    ∃ generation stamp mtu,
      r.value = true ∧ Staged.stagedAt r.before pid = some (stamp,[]) ∧
      r.before.dev.map Device.mtu = some mtu ∧
      let added : List Packet := [{mtu}]
      let event := Event.keepalivePrepared pid r
      let next := appendBirths ledger history.length (.staged generation pid stamp) added
      Valid (births ++ freshTickets history.length 0 added) next ∧
        Bounded (history ++ [event]).length (births ++ freshTickets history.length 0 added) ∧
        QueueInv (history ++ [event]) next r.after ∧
        (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
          (ticket,Status.terminal outcome) ∈ next) := by
  obtain ⟨d,p,device,resident,outcome⟩ := Staged.keepalive_prepare pid r run
  rcases outcome with ⟨_,_,same⟩ | ⟨_,_,same⟩ | ⟨empty,ready,changed⟩
  · exact Or.inl ⟨same,validBefore,bounded_mono bounded (by simp),same ▸ before.append_history _⟩
  · exact Or.inl ⟨same,validBefore,bounded_mono bounded (by simp),same ▸ before.append_history _⟩
  · have epoch : Packets.epoch r.before = some d.ifindex := by simp [Packets.epoch,device]
    have sameEpoch : Packets.epoch r.after = Packets.epoch r.before := by
      simp [Packets.epoch,changed,device]
    have old : Staged.stagedAt r.before pid = some (p.internalId,[]) := by
      simp [Staged.stagedAt,device,resident,empty]
    have after : Staged.stagedAt r.after pid = some (p.internalId,[{mtu := d.mtu}]) := by
      simp [Staged.stagedAt,changed]
    have actualMtu : r.before.dev.map Device.mtu = some d.mtu := by simp [device]
    have others : ∀ other, pid ≠ other → Staged.stagedAt r.after other = Staged.stagedAt r.before other := by
      intro other different
      simp [Staged.stagedAt,changed,device,Std.TreeMap.getElem?_insert,different]
    have born : Aligned (Born (history ++ [Event.keepalivePrepared pid r]) d.ifindex pid p.internalId)
        (freshTickets history.length 0 [{mtu := d.mtu}]) [{mtu := d.mtu}] :=
      .cons (.keepalive r history [] d.mtu rfl run ready (sameEpoch.trans epoch) old after actualMtu) .nil
    exact Or.inr ⟨d.ifindex,p.internalId,d.mtu,ready,old,actualMtu,
      admission validBefore bounded before epoch sameEpoch old after others born⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission
