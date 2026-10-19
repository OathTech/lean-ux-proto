import Leanux.Proofs.WG.Progress.HandshakeCallerSuffixSource
import Leanux.Proofs.WG.Progress.ClearWorkerRecordSource
import Leanux.WG.Timers

/-! The five original timer callbacks preserve supplied-record suffixes
with concrete work queue, staging, endpoint and timer dependencies. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem clearPeerEndpointSrc_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | env_operation_fact dstCacheReset_retains
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_birthdate
    | env_operation_fact native_and
    | env_operation_fact native_or
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_fact native_map
    | env_operation_fact native_peerGet
    | env_operation_fact native_recordQueued
    | env_operation_fact native_peekQueued
    | env_operation_step

theorem purgeStagedPackets_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  repeat' first
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_birthdate
    | env_operation_fact native_and
    | env_operation_fact native_or
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_fact native_map
    | env_operation_fact native_peerGet
    | env_operation_fact native_recordQueued
    | env_operation_fact native_peekQueued
    | env_operation_step

theorem expiredRetransmitHandshake_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (expiredRetransmitHandshake pid) := by
  unfold expiredRetransmitHandshake
  simp only [discard,map_const,Function.comp_def]
  repeat' first
    | env_operation_fact delTimer_retains
    | env_operation_fact purgeStagedPackets_retains
    | env_operation_fact modPeerTimer_retains
    | env_operation_fact clearPeerEndpointSrc_retains
    | env_operation_fact queuedInitiation_retains
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_birthdate
    | env_operation_fact native_and
    | env_operation_fact native_or
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_fact native_map
    | env_operation_fact native_peerGet
    | env_operation_fact native_recordQueued
    | env_operation_fact native_peekQueued
    | env_operation_step

theorem expiredSendKeepalive_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (expiredSendKeepalive pid) := by
  unfold expiredSendKeepalive
  simp only [discard,map_const,Function.comp_def]
  repeat' first
    | env_operation_fact keepalive_retains
    | env_operation_fact modPeerTimer_retains
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_birthdate
    | env_operation_fact native_and
    | env_operation_fact native_or
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_fact native_map
    | env_operation_fact native_peerGet
    | env_operation_fact native_recordQueued
    | env_operation_fact native_peekQueued
    | env_operation_step

theorem expiredNewHandshake_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (expiredNewHandshake pid) := by
  unfold expiredNewHandshake
  repeat' first
    | env_operation_fact clearPeerEndpointSrc_retains
    | env_operation_fact queuedInitiation_retains
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_birthdate
    | env_operation_fact native_and
    | env_operation_fact native_or
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_fact native_map
    | env_operation_fact native_peerGet
    | env_operation_fact native_recordQueued
    | env_operation_fact native_peekQueued
    | env_operation_step

theorem expiredZeroKeyMaterial_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  repeat' first
    | env_operation_fact peerPut_retains
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_birthdate
    | env_operation_fact native_and
    | env_operation_fact native_or
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_fact native_map
    | env_operation_fact native_peerGet
    | env_operation_fact native_recordQueued
    | env_operation_fact native_peekQueued
    | env_operation_step

theorem expiredSendPersistentKeepalive_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (expiredSendPersistentKeepalive pid) := by
  unfold expiredSendPersistentKeepalive
  repeat' first
    | env_operation_fact keepalive_retains
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_birthdate
    | env_operation_fact native_and
    | env_operation_fact native_or
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_fact native_map
    | env_operation_fact native_peerGet
    | env_operation_fact native_recordQueued
    | env_operation_fact native_peekQueued
    | env_operation_step

theorem timerCallback_retains (records : List HiddenRecord) (pid : PeerId) (timer : PeerTimer) :
    NativeKeeps records (timerCallback pid timer) := by
  cases timer
  · exact expiredRetransmitHandshake_retains records pid
  · exact expiredSendKeepalive_retains records pid
  · exact expiredNewHandshake_retains records pid
  · exact expiredZeroKeyMaterial_retains records pid
  · exact expiredSendPersistentKeepalive_retains records pid


theorem timerSection_strict (records : List HiddenRecord)
    (worker : Worker) (pid : PeerId) (timer : PeerTimer) :
    Hoare (Env.runTimerSection worker (liftWG (timerCallback pid timer)))
      (fun w=>Tail records w.ambient.hidden)
      (fun _ w=>StrictTail records w.ambient.hidden) := by
  unfold Env.runTimerSection
  split
  · exact hoare_throw _
  · dsimp only
    apply hoare_bind _ _ (modifyAmbient_hidden records
      (fun a=>{a with fired:=a.fired.push worker.symbol}) (fun _=>rfl))
    intro _
    exact runWorker_strict records worker _
      (native_product records _ (timerCallback_retains records pid timer))

end Leanux.Proofs.WG.Progress.RecordSuffix
