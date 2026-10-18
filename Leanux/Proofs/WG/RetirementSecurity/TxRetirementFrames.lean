import Leanux.Proofs.WG.RetirementSecurity.OwnershipCompletionFrames
import Leanux.Proofs.WG.RetirementSecurity.TxDisposeHolders

/-! Concrete disposal prerequisites through native completion. Packet-head
separation uses the actual logical TX queues. Peer final-release safety is
transported using campaign 1's actual peer-reference handoff equation; that
peer equation is never used as funding for a key reference. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem ownershipPoint_replace (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (fields : peerOwnership q = peerOwnership p) :
    ownershipPointView (replacePeer w d pid q) = ownershipPointView w := by
  unfold ownershipPointView keyReferenceView
  dsimp only [keyAt,ownershipAt,peerAt,packetKeyWords]
  simp only [replacePeer,device,Option.bind_some,Option.isSome_some,Prod.mk.injEq,
    true_and,and_true]
  funext other
  by_cases eq : pid = other
  · subst other; simp [found,fields]
  · simp [Std.TreeMap.getElem?_insert,eq]

/-- The selected logical head shares no packet head with any remaining
batch of its peer or any batch belonging to another peer. Multiplicity of
queued batch occurrences is retained. -/
def TxSeparated (pid : PeerId) (w : WGWorld) : Prop :=
  ∀ p, peerAt w pid = some p → ∀ items rest, p.txQueue.all = items :: rest →
    ∀ other q, peerAt w other = some q → ∀ batch,
      batch ∈ (if pid = other then rest else q.txQueue.all) →
      ∀ head, batch.head? = some head → head ∉ items

theorem TxSeparated.points (separated : TxSeparated pid w)
    (same : ownershipPointView v = ownershipPointView w) : TxSeparated pid v := by
  intro p found items rest selected other q otherFound batch member head first
  have cells : ∀ id, ownershipAt v id = ownershipAt w id :=
    fun id => congrFun (congrArg (fun x => x.2.2.1) same) id
  have this : ownershipAt w pid = some (peerOwnership p) := by
    rw [← cells]; simp [ownershipAt,found]
  have that : ownershipAt w other = some (peerOwnership q) := by
    rw [← cells]; simp [ownershipAt,otherFound]
  obtain ⟨old,oldFound,oldFields⟩ := Option.map_eq_some_iff.mp this
  obtain ⟨oldOther,oldOtherFound,otherFields⟩ := Option.map_eq_some_iff.mp that
  have queue : old.txQueue.all = p.txQueue.all := congrArg (fun x => x.2.1) oldFields
  have otherQueue : oldOther.txQueue.all = q.txQueue.all := congrArg (fun x => x.2.1) otherFields
  exact separated old oldFound items rest (queue.trans selected) other oldOther oldOtherFound
    batch (by simpa only [otherQueue] using member) head first

/-- Every resident selected peer is live; a sole remaining peer reference
may be paid only after its key slots have been cleared. -/
def PeerReleaseFunded (pid : PeerId) (w : WGWorld) : Prop :=
  ∀ p, peerAt w pid = some p → 0 < p.refcount ∧
    (p.refcount = 1 → p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)

theorem PeerReleaseFunded.ready (funded : PeerReleaseFunded pid w) : PeerReleaseReady pid w :=
  fun p found => (funded p found).2

theorem TxDetached.points (detached : TxDetached items w)
    (same : ownershipPointView v = ownershipPointView w) : TxDetached items v := by
  intro pid p found batch member head first
  have point : ownershipAt v pid = ownershipAt w pid := congrFun (congrArg (fun x => x.2.2.1) same) pid
  have after : ownershipAt v pid = some (peerOwnership p) := by simp [ownershipAt,found]
  obtain ⟨old,resident,fields⟩ := Option.map_eq_some_iff.mp (point.symm.trans after)
  have queue : old.txQueue.all = p.txQueue.all := congrArg (fun x => x.2.1) fields
  exact detached pid old resident batch (queue ▸ member) head first

theorem transfer_peer_growth (step : Queues.RxCredits.Handoff w v [] [] delta)
    (found : peerAt v pid = some p) :
    ∃ old, peerAt w pid = some old ∧ old.refcount ≤ p.refcount := by
  obtain ⟨vd,device,stored⟩ := Option.bind_eq_some_iff.mp found
  have epoch := congrArg Prod.fst step.base
  cases oldDevice : w.dev with
  | none => simp [Queues.RxCredits.baseView,device,oldDevice] at epoch
  | some wd =>
    have epochEq : vd.ifindex = wd.ifindex := by
      simpa only [Queues.RxCredits.baseView,device,oldDevice,Option.map_some,Option.some.injEq] using epoch
    have cell := congrFun (congrArg Prod.snd step.base) pid
    have mapped : (wd.peers[pid]?).map (fun q => (q.internalId,q.rxQueue)) =
        some (p.internalId,p.rxQueue) := by
      simpa only [Queues.RxCredits.baseView,device,oldDevice,Option.bind_some,stored,Option.map_some]
        using cell.symm
    obtain ⟨old,oldStored,fields⟩ := Option.map_eq_some_iff.mp mapped
    have stamp : old.internalId = p.internalId := congrArg Prod.fst fields
    have count := step.count ⟨vd.ifindex,pid,p.internalId⟩
    simp only [List.count_nil,Nat.add_zero] at count
    have beforeBalance : Queues.RxCredits.balance w ⟨vd.ifindex,pid,p.internalId⟩ = old.refcount := by
      simp [Queues.RxCredits.balance,Queues.RxCredits.resident,oldDevice,oldStored,epochEq,stamp]
    have afterBalance : Queues.RxCredits.balance v ⟨vd.ifindex,pid,p.internalId⟩ = p.refcount := by
      simp [Queues.RxCredits.balance,Queues.RxCredits.resident,device,stored]
    refine ⟨old,by simp [peerAt,oldDevice,oldStored],?_⟩
    rw [beforeBalance,afterBalance] at count
    omega

theorem completion_peer_growth (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((createDataDone pid items).run w).run a = .ok (((),v),b))
    (found : peerAt v other = some p) :
    ∃ old, peerAt w other = some old ∧ old.refcount ≤ p.refcount := by
  rw [Queues.RxCredits.TxReservation.completion_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,prefixRun,fresh⟩ := run
  obtain ⟨delta,step⟩ := (Queues.RxCredits.Transfers.iff_run_ambient _).mp
    (Queues.RxCredits.TxReservation.keepKeyFresh_transfers pid) u c () v b fresh
  obtain ⟨middle,middleFound,growth⟩ := transfer_peer_growth step found
  have carrier := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.RxCredits.TxReservation.completionPrefix_carrier pid items) w a () u c prefixRun
  have point := congrFun (congrArg (fun x => x.1.2) carrier) other
  have mapped : (peerAt w other).map (fun q => (q.internalId,q.refcount,q.rxQueue)) =
      some (middle.internalId,middle.refcount,middle.rxQueue) := by
    change (peerAt u other).map (fun q => (q.internalId,q.refcount,q.rxQueue)) =
      (peerAt w other).map (fun q => (q.internalId,q.refcount,q.rxQueue)) at point
    simpa only [middleFound,Option.map_some] using point.symm
  obtain ⟨old,oldFound,fields⟩ := Option.map_eq_some_iff.mp mapped
  have count : old.refcount = middle.refcount := congrArg (fun x => x.2.1) fields
  exact ⟨old,oldFound,count.symm ▸ growth⟩

theorem PeerReleaseFunded.complete (funded : PeerReleaseFunded other w)
    (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((createDataDone pid items).run w).run a = .ok (((),v),b)) :
    PeerReleaseFunded other v := by
  intro p found
  obtain ⟨old,oldFound,growth⟩ := completion_peer_growth pid items a b run found
  obtain ⟨positive,cleared⟩ := funded old oldFound
  refine ⟨by omega,?_⟩
  intro final
  have oldFinal : old.refcount = 1 := by omega
  have slots := cleared oldFinal
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (createDataDone_ownership pid items) w a () v b run
  have point : ownershipAt v other = ownershipAt w other :=
    congrFun (congrArg (fun x => x.2.2.1) same) other
  have fields : peerOwnership p = peerOwnership old := by
    simpa only [ownershipAt,found,oldFound,Option.map_some,Option.some.injEq] using point
  have slot := congrArg Prod.fst fields
  simpa only [peerOwnership,slotFields,Prod.mk.injEq] using slot.trans
    (show slotFields old = (none,none,none) from by simp [slotFields,slots.1,slots.2.1,slots.2.2])

end Leanux.Proofs.WG.RetirementSecurity
