import Leanux.Proofs.WG.Progress.EncryptSuffixFrames
import Leanux.Proofs.WG.Progress.StagingSuffixSource
import Leanux.Proofs.WG.Progress.CutJitterSuffixSource
import Leanux.Proofs.WG.Index.EncryptRuleSource

/-! Original encrypt packet, publication and tail suffix contracts. The NAPI
callback remains explicit only in the complete step/iteration adapters. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Index Queues

theorem padding_retains (records : List HiddenRecord) (len mtu : Nat) :
    NativeKeeps records (calculateSkbPadding len mtu) := by
  unfold calculateSkbPadding
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_branchCmp records _ _ _ _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem encryptPublish_retains (records : List HiddenRecord) (item : List SkbId) (state : PacketState) :
    NativeKeeps records (enqueuePerPeerTx item state) :=
  native_of_staging_rule records _ (StagingAmbientRules.enqueuePerPeerTx_rule item state (stagingContracts records))

theorem encryptPoll_retains (records : List HiddenRecord) :
    NativeKeeps records TxRing.pollSource := by
  unfold TxRing.pollSource
  exact native_bind records _ _ (native_getDev records) (fun _=>
    native_bind records _ _ (native_modifyDev records _) (fun _=>native_pure records _))

theorem encryptPacket_retains (records : List HiddenRecord) (key : KeypairId) (packet : DataPacket) :
    Preserves (fun w : World=>Tail records w.ambient.hidden)
      (encryptPacket Env.checksumHelp key packet) :=
  EncryptCore.packet_preserves_leaves _ key packet
    (native_product records _ (padding_retains records _ _))
    (checksum_retains records)
    (native_product records _ (native_getKeypair records key))
    (liftAmbient_contract _ _ _ (skipCut_retains _ records))
    (fun site=>liftAmbient_contract _ _ _ (hiddenAlloc_retains site records))
    (product_branch_retains records)

theorem encryptStepTail_retains (records : List HiddenRecord) (item : Option (List SkbId)) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (RxWorkers.encryptStepTailSource item) :=
  EncryptCore.stepTail_preserves_leaves _ item
    (fun id=>native_product records _ (native_getTx records id))
    (fun id f=>native_product records _ (native_setTx records id f))
    (fun xs state=>native_product records _ (encryptPublish_retains records xs state))
    (encryptPacket_retains records) (product_branch_retains records) (product_invariant_retains records)

theorem encryptTail_retains (records : List HiddenRecord) (item : Option (List SkbId)) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (RxWorkers.encryptTailSource item) :=
  EncryptCore.tail_preserves_leaves _ item
    (fun id=>native_product records _ (native_getTx records id))
    (fun id f=>native_product records _ (native_setTx records id f))
    (fun xs state=>native_product records _ (encryptPublish_retains records xs state))
    (encryptPacket_retains records) (condResched_retains _ records)
    (product_branch_retains records) (product_invariant_retains records)

theorem encryptIteration_retains (records : List HiddenRecord) (softirq : Leanux.M Unit)
    (softKeeps : Preserves (fun w : World=>Tail records w.ambient.hidden) softirq) :
    Preserves (fun w : World=>Tail records w.ambient.hidden)
      (encryptIter Env.checksumHelp softirq (Env.condResched .encryptWorker)) := by
  rw [RxWorkers.encrypt_source]
  exact preserves_bind (native_product records _ (encryptPoll_retains records)) (fun item=>
    preserves_bind softKeeps (fun _=>encryptTail_retains records item))

theorem encryptStep_factor (softirq : Leanux.M Unit) :
    encryptStep Env.checksumHelp softirq =
      (do let item←liftWG TxRing.pollSource; softirq; RxWorkers.encryptStepTailSource item) := by
  simp only [encryptStep,encryptRingPoll,TxRing.pollSource,RxWorkers.encryptStepTailSource,
    liftWG_bind,liftWG_pure,bind_assoc,pure_bind]
  rfl

theorem encryptStep_retains (records : List HiddenRecord) (softirq : Leanux.M Unit)
    (softKeeps : Preserves (fun w : World=>Tail records w.ambient.hidden) softirq) :
    Preserves (fun w : World=>Tail records w.ambient.hidden)
      (encryptStep Env.checksumHelp softirq) := by
  rw [encryptStep_factor]
  exact preserves_bind (native_product records _ (encryptPoll_retains records)) (fun item=>
    preserves_bind softKeeps (fun _=>encryptStepTail_retains records item))

end Leanux.Proofs.WG.Progress.RecordSuffix
