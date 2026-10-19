import Leanux.Proofs.WG.RetirementSecurity.TxWorkPublicationCoverage
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageCreate

/-! Refusal cleanup preserves reverse service obligations for every other
queued batch. The freed batch is the actual detached unpublished local. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem Obligations.head_frames (before : Obligations crypt tx w)
    (queues : txQueueContents v=txQueueContents w)
    (cells : ∀pid p,peerAt w pid=some p→∀batch∈p.txQueue.all,∀first,
      batch.head?=some first→TxDisposition.txPackets v first=TxDisposition.txPackets w first)
    (ring : txCryptItems v=txCryptItems w) (work : queued v=queued w) : Obligations crypt tx v := by
  constructor
  · intro pid p found batch member
    obtain ⟨q,stored,prior⟩:=queue_member (queues ▸ (queue_contents found).symm ▸ member)
    obtain ⟨first,packet,head,resident,pending⟩:=before.batches pid q stored batch prior
    exact ⟨first,packet,head,(cells pid q stored batch prior first head).trans resident,
      by simpa only [ring] using pending⟩
  · intro pid p found batch first packet headQueue head resident terminal
    have selected:(txQueueContents w pid).head?=some batch := by
      rw [←queues,queue_contents found]
      exact headQueue
    obtain ⟨q,stored,member⟩:=queue_member (List.mem_of_head? selected)
    have headOld:q.txQueue.all.head?=some batch := by simpa only [queue_contents stored] using selected
    simpa only [work] using before.heads pid q stored batch first packet headOld head
      ((cells pid q stored batch member first head).symm.trans resident) terminal

theorem Obligations.key_put (before : Obligations crypt tx w) (kid : Option KeypairId) (now : Bool)
    (a b : Ambient) (run : ((keypairPut kid now).run w).run a=.ok (((),v),b)) :
    Obligations crypt tx v :=
  before.contents (queueContents_of_peers (put_peers kid now w v a b run))
    ((ProjectedAction.iff_run_ambient _ _ _).mp (TxDisposition.keyPut_packets kid now) w a () v b run)
    (crypt_items_eq ((ProjectedAction.iff_run_ambient _ _ _).mp (TxRing.keypairPut_frame kid now) w a () v b run))
    ((ProjectedAction.iff_run_ambient _ _ _).mp (TxWork.key_put kid now) w a () v b run)

theorem Obligations.peer_put (before : Obligations crypt tx w) (pid : Option PeerId)
    (a b : Ambient) (run : ((peerPut pid).run w).run a=.ok (((),v),b)) :
    Obligations crypt tx v :=
  before.contents ((ProjectedAction.iff_run_ambient _ _ _).mp (queueContents_peer_put pid) w a () v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (TxDisposition.peerPut_packets pid) w a () v b run)
    (crypt_items_eq ((ProjectedAction.iff_run_ambient _ _ _).mp (TxRing.peerPut_frame pid) w a () v b run))
    ((ProjectedAction.iff_run_ambient _ _ _).mp (TxWork.peer_put pid) w a () v b run)

theorem free_list_work (items : List SkbId) : SameView queued (TxDisposition.freeList items) := by
  induction items with
  | nil=>simpa only [TxDisposition.freeList_nil] using SameView.pure queued ()
  | cons id rest ih=>
    rw [TxDisposition.freeList_cons]
    apply SameView.bind ?_ (fun _=>ih)
    intro initial
    unfold freeTxSkb
    apply hoare_liftSkb
    intro w d store before device
    simpa only [queued,device,Option.map_some,Option.getD_some] using before

theorem Obligations.free_list (before : Obligations crypt tx w)
    (inventory : TxInventory (held::locals) w) (a b : Ambient)
    (run : ((TxDisposition.freeList held.items).run w).run a=.ok (((),v),b)) :
    Obligations crypt tx v := by
  apply before.head_frames
    (queueContents_of_peers ((ProjectedAction.iff_run_ambient _ _ _).mp
      (free_list_peer_frame held.items) w a () v b run))
    ?_
    (crypt_items_eq ((ProjectedAction.iff_run_ambient _ _ _).mp (free_list_ring held.items) w a () v b run))
    ((ProjectedAction.iff_run_ambient _ _ _).mp (free_list_work held.items) w a () v b run)
  intro pid p found batch member first head
  have outside:first∉held.items := by
    intro inside
    exact inventory.localsSeparate pid p found first (by simp [txLocalItems,inside])
      (List.mem_flatten.mpr ⟨batch,member,List.mem_of_head? head⟩)
  exact (ProjectedAction.iff_run_ambient _ _ _).mp
    (TxDisposition.MarkTransport.free_other first held.items outside) w a () v b run

theorem Obligations.cleanup (before : Obligations crypt tx w)
    (inventory : TxInventory (⟨.unpublished,pid,items⟩::locals) w)
    (first : SkbId) (a b : Ambient)
    (run : ((TxDisposition.cleanupSource pid items first).run w).run a=.ok (((),v),b)) :
    Obligations crypt tx v := by
  simp only [TxDisposition.cleanupSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨packet,u,c,readRun,_,t,e,keyRun,_,s,f,peerRun,freeRun⟩:=run
  obtain ⟨same,clock,_,_,_⟩:=Packets.getTxSkb_current first w u packet a c readRun
  subst u
  subst c
  have middle:=(before.key_put (some packet.keypair) false a e keyRun).peer_put (some pid) e f peerRun
  have owned:=(inventory.key_put (some packet.keypair) false a e keyRun).peer_put (some pid) e f peerRun
  exact middle.free_list owned f b freeRun

end Leanux.Proofs.WG.RetirementSecurity.TxWork
