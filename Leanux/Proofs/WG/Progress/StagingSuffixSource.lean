import Leanux.Proofs.WG.Index.StagingAmbientRulesSource
import Leanux.Proofs.WG.Progress.QueueSuffixSource
import Leanux.Proofs.WG.Progress.TimerHookSuffixSource
import Leanux.Proofs.WG.Progress.ReleaseSuffixSource

/-! Concrete original staging and queueing paths retain the ambient supplied-record suffix on normal return. Every callback in the generic source contract is discharged here; original Stops and finite evaluation remain separate. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Noise
open Leanux.Proofs.WG.Index

theorem native_getTx (records : List HiddenRecord) (id : SkbId) :
    NativeKeeps records (getTxSkb id) := by
  apply native_liftSkb
  intro s
  unfold SkbStore.getTx
  simp only [StateT.run_bind,StateT.run_get,pure_bind]
  split
  · exact preserves_pure _
  · exact ambient_stop _ _

theorem native_setTx (records : List HiddenRecord) (id : SkbId) (f : DataPacket → DataPacket) :
    NativeKeeps records (setTxSkb id f) := by
  apply native_liftSkb
  intro s
  unfold SkbStore.setTx SkbStore.getTx
  simp only [StateT.run_bind,StateT.run_get,pure_bind]
  split
  · exact preserves_pure _
  · exact ambient_stop _ _

theorem native_freeTx (records : List HiddenRecord) (id : SkbId) :
    NativeKeeps records (freeTxSkb id) := by
  apply native_liftSkb
  intro s
  unfold SkbStore.freeTx SkbStore.getTx
  simp only [StateT.run_bind,StateT.run_get,pure_bind]
  split
  · exact preserves_pure _
  · exact ambient_stop _ _

theorem native_newTx (records : List HiddenRecord) (pkt : DataPacket) :
    NativeKeeps records (newTxSkb pkt) := by
  apply native_liftSkb
  intro s
  exact preserves_pure _

theorem native_refcountIncNotZero (records : List HiddenRecord) (count : Nat) :
    NativeKeeps records (refcountIncNotZero count : WG.M Bool) := by
  unfold refcountIncNotZero
  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head branchCmp; exact native_branchCmp records _ _ _ _)
    | (native_suffix_head unsupported; exact native_unsupported records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem keypairGet_retains (records : List HiddenRecord) (kid : Option KeypairId) :
    NativeKeeps records (keypairGet kid) := by
  unfold keypairGet
  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head getKeypair; exact native_getKeypair records _)
    | (native_suffix_head setKeypair; exact native_setKeypair records _ _)
    | (native_suffix_head refcountIncNotZero; exact native_refcountIncNotZero records _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem cpumaskChoose_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp only [Nat.mod_one]
  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | (native_suffix_head ForIn.forIn; simpa using native_pure records PUnit.unit)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem ecnEncap_retains (records : List HiddenRecord) (pkt : Packet) :
    NativeKeeps records (ipTunnelEcnEncap pkt) := by
  unfold ipTunnelEcnEncap ipTunnelGetDsfield Packet.protocol
  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head unsupported; exact native_unsupported records _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem staging_rule_of_native {α : Type} (records : List HiddenRecord) (action : WG.M α)
    (keep : NativeKeeps records action) :
    StagingAmbientRules.Ensures action (fun _ a=>Tail records a.hidden) (fun _ _ a=>Tail records a.hidden) :=
  fun g a value after b pre run=>(hoare_iff_run _ _ _).mp (keep g) a (value,after) b pre run

theorem native_of_staging_rule {α : Type} (records : List HiddenRecord) (action : WG.M α)
    (keep : StagingAmbientRules.Ensures action (fun _ a=>Tail records a.hidden) (fun _ _ a=>Tail records a.hidden)) :
    NativeKeeps records action := by
  intro g
  apply (hoare_iff_run _ _ _).mpr
  intro a value b pre run
  exact keep g a value.1 value.2 b pre run

def stagingContracts (records : List HiddenRecord) :
    StagingAmbientRules.Contracts (fun _ a=>Tail records a.hidden) where
  peer := fun _ _=>True
  key := fun _ _=>True
  readPeer := fun pid {_} _ good=>
    staging_rule_of_native records _ (native_bind records _ _ (native_getPeer records pid)
      (fun p=>native_of_staging_rule records _ (good p True.intro)))
  readKey := fun kid {_} _ good=>
    staging_rule_of_native records _ (native_bind records _ _ (native_getKeypair records kid)
      (fun p=>native_of_staging_rule records _ (good p True.intro)))
  setPeer := fun pid p _=>staging_rule_of_native records _ (native_setPeer records pid p)
  setKey := fun kid k _=>staging_rule_of_native records _ (native_setKeypair records kid k)
  modify := fun f _ _ _ _=>staging_rule_of_native records _ (native_modifyDev records f)
  peerGet := fun pid=>staging_rule_of_native records _ (native_peerGet records pid)
  peerPut := fun pid=>staging_rule_of_native records _ (peerPut_retains records pid)
  keyGet := fun kid=>staging_rule_of_native records _ (keypairGet_retains records kid)
  release := fun kid now=>staging_rule_of_native records _ (keypairPut_retains records kid now)
  getTx := fun id=>staging_rule_of_native records _ (native_getTx records id)
  setTx := fun id f=>staging_rule_of_native records _ (native_setTx records id f)
  freeTx := fun id=>staging_rule_of_native records _ (native_freeTx records id)
  newTx := fun pkt=>staging_rule_of_native records _ (native_newTx records pkt)
  branch := fun site value=>staging_rule_of_native records _ (native_branch records site value)
  cmp := fun site value lhs rhs=>staging_rule_of_native records _ (native_branchCmp records site value lhs rhs)
  clock := fun site=>staging_rule_of_native records _ (native_clock records site)
  peek := fun worker pid=>staging_rule_of_native records _ (native_peekQueued records worker pid)
  queue := fun worker pid=>staging_rule_of_native records _ (native_recordQueued records worker pid)
  deviceQueue := fun worker=>staging_rule_of_native records _ (native_queueDeviceWork records worker)
  ecn := fun pkt=>staging_rule_of_native records _ (ecnEncap_retains records pkt)
  cpu := fun pid=>staging_rule_of_native records _ (cpumaskChoose_retains records pid)

theorem queuedInitiation_retains (records : List HiddenRecord) (pid : PeerId) (retry : Bool) :
    NativeKeeps records (sendQueuedHandshakeInitiation pid retry) :=
  native_of_staging_rule records _ (StagingAmbientRules.sendQueuedHandshakeInitiation_rule pid retry (stagingContracts records))

theorem staged_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (sendStagedPackets pid) :=
  native_of_staging_rule records _ (StagingAmbientRules.sendStagedPackets_rule pid (stagingContracts records))

theorem keepKeyFreshRx_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (keepKeyFreshRx pid) :=
  Completion.fresh_retains records pid (queuedInitiation_retains records pid false)

theorem prepareRest_retains (records : List HiddenRecord) (pid : PeerId) (pkt : RxPacket) :
    NativeKeeps records (Leanux.Proofs.WG.Queues.RxCredits.prepareRest pid pkt) :=
  Completion.prepare_retains records pid pkt (keepKeyFreshRx_retains records pid)
    (timersAnyReceived_retains records pid) (timersTraversal_retains records pid)
    (timersDataReceived_retains records pid)

theorem keepalive_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (sendKeepalive pid) :=
  native_of_staging_rule records _ (StagingAmbientRules.keepalive_rule pid
    (fun _ a=>Tail records a.hidden) (fun _ a=>Tail records a.hidden)
    (fun _ _ h=>h) (staging_rule_of_native records _ (staged_retains records pid))
    (fun _ _ _ _ _ _ _ h=>h)
    (fun site value=>staging_rule_of_native records _ (native_branch records site value))
    (staging_rule_of_native records _ (native_alloc records .keepaliveSkb)))
end Leanux.Proofs.WG.Progress.RecordSuffix
