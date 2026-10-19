import Leanux.Proofs.WG.RetirementSecurity.TxWorkPublication
import Leanux.Proofs.WG.RetirementSecurity.TxCoverage

/-! The reverse work-coverage obligations needed before device teardown.
Every uncrypted queued batch has a ring/selected-worker alias. Only a terminal
queue head requires a queued or active TX actor: a DEAD tail may wait behind an
uncrypted head. These are explicit local predicates, not initialized facts. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

structure Obligations (crypt : List (List SkbId)) (tx : List PeerId) (w : WGWorld) : Prop where
  batches : ∀pid p,peerAt w pid=some p→∀batch∈p.txQueue.all,
    ∃first packet,batch.head?=some first ∧ TxDisposition.txPackets w first=some packet ∧
      (packet.state=.uncrypted→batch∈txCryptItems w++crypt)
  heads : ∀pid p,peerAt w pid=some p→∀batch first packet,
    p.txQueue.all.head?=some batch→batch.head?=some first→
    TxDisposition.txPackets w first=some packet→packet.state≠.uncrypted→pid∈queued w++tx

theorem initial (net bare : Bool) : Obligations [] [] (Runner.initialWG net bare) := by
  constructor
  · intro pid p found
    cases net <;> cases bare <;> simp [peerAt,Runner.initialWG] at found
  · intro pid p found
    cases net <;> cases bare <;> simp [peerAt,Runner.initialWG] at found

theorem Obligations.frame (before : Obligations crypt tx w)
    (queues : Queues.RxCredits.handoffTxView v=Queues.RxCredits.handoffTxView w)
    (packets : TxDisposition.txPackets v=TxDisposition.txPackets w)
    (ring : txCryptItems v=txCryptItems w) (work : queued v=queued w) :
    Obligations crypt tx v := by
  have original (pid : PeerId) (p : Peer) (found : peerAt v pid=some p) :
      ∃q,peerAt w pid=some q ∧ p.txQueue.all=q.txQueue.all := by
    have equal:=congrFun queues pid
    change (peerAt v pid).map (·.txQueue.all)=(peerAt w pid).map (·.txQueue.all) at equal
    rw [found] at equal
    obtain ⟨q,stored,same⟩:=Option.map_eq_some_iff.mp equal.symm
    exact ⟨q,stored,same.symm⟩
  constructor
  · intro pid p found batch member
    obtain ⟨q,stored,same⟩:=original pid p found
    obtain ⟨first,packet,head,resident,pending⟩:=before.batches pid q stored batch (same ▸ member)
    exact ⟨first,packet,head,packets.symm ▸ resident,by simpa only [ring] using pending⟩
  · intro pid p found batch first packet queue head resident terminal
    obtain ⟨q,stored,same⟩:=original pid p found
    simpa only [work] using before.heads pid q stored batch first packet (same ▸ queue)
      head (packets ▸ resident) terminal

theorem no_queues (coverage : Obligations [] [] w) (ring : txCryptItems w=[])
    (work : queued w=[]) : ∀pid p,peerAt w pid=some p→p.txQueue.all=[] := by
  intro pid p found
  cases queue:p.txQueue.all with
  | nil=>rfl
  | cons batch rest=>
    obtain ⟨first,packet,head,resident,pending⟩:=coverage.batches pid p found batch (by simp [queue])
    by_cases uncrypted:packet.state=.uncrypted
    · have member:=pending uncrypted
      simp [ring] at member
    · have member:=coverage.heads pid p found batch first packet (by simp [queue]) head resident uncrypted
      simp [work] at member

/-- Empty actual queues imply no resident allocation only with the converse
resident-coverage theorem. Unique aliases alone cannot justify this step. -/
theorem no_packets (obligations : Obligations [] [] w) (coverage : TxCoverage [] w)
    (ring : txCryptItems w=[]) (work : queued w=[]) : TxDisposition.txPackets w=fun _=>none := by
  funext id
  cases resident:TxDisposition.txPackets w id with
  | none=>rfl
  | some packet=>
    rcases coverage id packet resident with impossible | ⟨pid,member⟩
    · simp [txLocalItems] at impossible
    · change id∈(((peerAt w pid).map (·.txQueue.all)).getD []).flatten at member
      cases found:peerAt w pid with
      | none=>simp [found] at member
      | some p=>simp [found,no_queues obligations ring work pid p found] at member

/-- The native empty-ring guard is about the physical consumer head. Its
initialized ring refinement makes it equivalent to an empty logical live list,
including a zero-size ring and stale occupied slots. -/
theorem ring_empty (physical : TxRing.Refines (PtrRing.init n) h r)
    (empty : r.empty=true) : r.items=[] := by
  by_cases positive:0<n
  · obtain ⟨t,retired,stale,live,bounds,equal,_,_⟩:=physical.initialized.1 positive
    rw [equal,PtrRing.empty,Ring.peek bounds] at empty
    have nil:live=[] := by cases live <;> simp_all
    rw [equal,Ring.items bounds,nil]
  · have zero:n=0 := by omega
    subst n
    obtain ⟨commands,run⟩:=physical
    rw [Ring.Journal.run_zero _ (by rfl)] at run
    have same:r=PtrRing.init 0 := (congrArg Prod.snd run).symm
    simp [same,PtrRing.items,PtrRing.count,PtrRing.init]

theorem guarded_no_packets (obligations : Obligations [] [] w) (coverage : TxCoverage [] w)
    (physical : TxDisposition.LiveFrontier.Physical w) (device : w.dev=some d)
    (cryptEmpty : d.encryptQueue.empty=true) (txEmpty : d.txWorkQueue.isEmpty=true) :
    TxDisposition.txPackets w=fun _=>none := by
  obtain ⟨n,h,refines⟩:=physical d device
  apply no_packets obligations coverage
  · simpa only [txCryptItems,device,Option.map_some,Option.getD_some] using ring_empty refines cryptEmpty
  · simpa only [queued,device,Option.map_some,Option.getD_some] using List.isEmpty_iff.mp txEmpty

end Leanux.Proofs.WG.RetirementSecurity.TxWork
