import Leanux.Proofs.WG.RetirementSecurity.RemovalOwnershipFrames

/-! Detaching a peer's base-list entry transfers its real retained peer
reference into the removal caller's loans. Key slots remain covered until
later clear; publication removal is not allocation destruction. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem SlotPeerReferences.transport (before : SlotPeerReferences holders loans w)
    (peers : peerView v = peerView w) (ownership : ownershipPointView v = ownershipPointView w)
    (references : (holders.base ++ loans).Perm (holders'.base ++ loans')) :
    SlotPeerReferences holders' loans' v := by
  intro d pid p device stored slots
  have epoch := congrArg Prod.fst peers
  cases oldDevice : w.dev with
  | none => simp [peerView,device,oldDevice] at epoch
  | some old =>
    have sameEpoch : d.ifindex = old.ifindex := by
      simpa only [peerView,device,oldDevice,Option.map_some,Option.some.injEq] using epoch
    have cell := congrFun (congrArg Prod.snd peers) pid
    have mapped : (old.peers[pid]?).map (fun q => (q.internalId,q.refcount,q.rxQueue)) =
        some (p.internalId,p.refcount,p.rxQueue) := by
      simpa only [peerView,device,oldDevice,Option.bind_some,stored,Option.map_some] using cell.symm
    obtain ⟨q,resident,fields⟩ := Option.map_eq_some_iff.mp mapped
    have stamp : q.internalId = p.internalId := congrArg Prod.fst fields
    have point := congrFun (congrArg (fun s => s.2.2.1) ownership) pid
    have sameOwnership : peerOwnership p = peerOwnership q := by
      simpa only [ownershipPointView,ownershipAt,peerAt,device,oldDevice,Option.bind_some,
        stored,resident,Option.map_some,Option.some.injEq] using point
    have sameSlots : slotFields p = slotFields q := congrArg Prod.fst sameOwnership
    have oldSlots : q.keypairNext ≠ none ∨ q.keypairPrevious ≠ none ∨ q.keypairCurrent ≠ none := by
      have props := congrArg (fun fields => fields.1 ≠ none ∨ fields.2.1 ≠ none ∨ fields.2.2 ≠ none) sameSlots
      exact props ▸ slots
    have anchored := before old pid q oldDevice resident oldSlots
    apply references.mem_iff.mp
    simpa only [sameEpoch,stamp] using anchored

/-- Native make-dead detaches the base holder without paying it. Both the
actual key account and its independent peer protection survive the original
routing/list updates; the detached base remains an explicit caller loan. -/
theorem SlotPeerReferences.make_dead (before : SlotPeerReferences holders loans w)
    (pid : PeerId) (a b : Ambient)
    (run : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    SlotPeerReferences (holders.withoutBase (BaseRemoval.live holders.base pid))
      (BaseRemoval.detached holders.base pid ++ loans) v := by
  apply before.transport
  · exact congrArg (fun s => s.1.1) (BaseRemoval.peerMakeDead_normal pid w v a b run).1
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp (makeDead_ownership pid) w a () v b run
  · simpa only [DurableHolders.withoutBase,List.append_assoc] using
      (BaseRemoval.partition holders.base pid).append_right loans

theorem make_dead_accounts (keys : HolderAccount temporary w)
    (peers : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (pid : PeerId) (a b : Ambient)
    (run : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v ∧
      (holders.withoutBase (BaseRemoval.live holders.base pid)).Funded carriers
        (BaseRemoval.detached holders.base pid ++ loans) v ∧
      StableRx carriers v ∧
      SlotPeerReferences (holders.withoutBase (BaseRemoval.live holders.base pid))
        (BaseRemoval.detached holders.base pid ++ loans) v := by
  have actual := DurableHolders.peerMakeDead_funded pid peers stable a b run
  exact ⟨keys.make_dead pid a b run,actual.1,actual.2,anchors.make_dead pid a b run⟩

end Leanux.Proofs.WG.RetirementSecurity
