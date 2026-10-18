import Leanux.Proofs.WG.Index.EncryptRuleSource
import Leanux.Proofs.WG.Index.EncryptCoreFrames
import Leanux.Proofs.WG.Index.StagingIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.EncryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem enqueue_core (item : List SkbId) (state : PacketState) :
    Preserves Reached.Core (enqueuePerPeerTx item state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  have rich := (hoare_iff_run_ambient _ _ _).mp
    (StagingRich.enqueuePerPeerTx_rich item state w) w a result v b (StagingRich.refl w) run
  have transfer := handoff_of_view
    ((ProjectedAction.iff_run_ambient _ _ _).mp (publication_protect item state) w a result v b run)
  exact StagingRich.core_handoff rich transfer pre

theorem poll_core : Preserves Reached.Core TxRing.pollSource := by
  unfold TxRing.pollSource
  apply preserves_bind (getDev_sameWGStore.wp
    (fun s=>∀d,s.dev=some d→DeviceIndexCore d))
  intro d
  apply preserves_bind
    (ConfigurationIndex.frame_core (ConfigurationIndex.modifyDev_fields
      (fun w=>{w with encryptQueue:=d.encryptQueue.consume.2}) (fun _=>rfl)))
  intro _
  exact preserves_pure _

theorem packet_core (key : KeypairId) (packet : DataPacket) :
    Preserves (fun w : World=>Reached.Core w.wg) (encryptPacket Env.checksumHelp key packet) := by
  apply packet_preserves_source
  · exact PublicationPoll.native_product _ _
      ((calculateSkbPadding_sameWGWorld _ _).wp Reached.Core)
  · exact fun p=>(checksumHelp_sameWorld p).wp (fun w : World=>Reached.Core w.wg)
  · apply PublicationPoll.native_product
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    exact (KeyTimes.getKeypair_return key w v result a b run).1 ▸ pre
  · intro α action
    exact productAmbient_spec action _ (fun _ _ pre=>pre)

theorem tail_core (item : Option (List SkbId)) :
    Preserves (fun w : World=>Reached.Core w.wg) (RxWorkers.encryptTailSource item) := by
  apply tail_preserves_source
  · intro id
    exact PublicationPoll.native_product _ _ (CryptCore.skb (SkbStore.getTx id))
  · intro id f
    exact PublicationPoll.native_product _ _ (CryptCore.skb (SkbStore.setTx id f))
  · intro item state
    exact PublicationPoll.native_product _ _ (enqueue_core item state)
  · exact packet_core
  · exact product_core_store _ (condResched_sameKernel _)
  · intro α action
    exact productAmbient_spec action _ (fun _ _ pre=>pre)

theorem poll_ready : Preserves TimerCore.Ready TxRing.pollSource := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp CurrentSlots.encryptPoll_preserves w a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp poll_core w a result v b pre.2 run⟩

theorem tail_ready (item : Option (List SkbId)) :
    Preserves (fun w : World=>TimerCore.Ready w.wg) (RxWorkers.encryptTailSource item) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  exact ⟨(hoare_iff_run _ _ _).mp (CurrentSlots.encryptTail_preserves item) w result v pre.1 run,
    (hoare_iff_run _ _ _).mp (tail_core item) w result v pre.2 run⟩

theorem original_ready
    (soft : Preserves (fun w : World=>TimerCore.Ready w.wg) Env.napiSoftirq) :
    Preserves (fun w : World=>TimerCore.Ready w.wg)
      (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  rw [RxWorkers.encrypt_source]
  apply preserves_bind (PublicationPoll.native_product _ _ poll_ready)
  intro item
  exact preserves_bind soft (fun _=>tail_ready item)

theorem observed (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (soft : Preserves (fun w : World=>TimerCore.Ready w.wg) Env.napiSoftirq) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.encryptIteration := by
  apply Reached.aux_pair _ initial loans before (HolderAuxScheduler.encrypt_preserves initial loans before)
  intro w h pre result v run
  have base := (BaseCoherence.encryptIteration_structure (BaseCoherence.view w.wg) w h rfl).choose_spec.2.2
  simp only [run] at base
  have core := (hoare_iff_run _ _ _).mp (original_ready soft) w result v ⟨pre.1.2.2,pre.2.2⟩
    ((RxHistory.encryptIteration_erases w h).symm.trans run)
  exact ⟨BaseCoherence.transport pre.2.1 base,core.2⟩

end Leanux.Proofs.WG.Index.EncryptCore
