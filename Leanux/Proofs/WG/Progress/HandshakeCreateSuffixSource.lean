import Leanux.Proofs.WG.Progress.HandshakeConsumeSuffixSource
import Leanux.Proofs.WG.Progress.IndexInsertSuffixSource

/-! Original handshake creators and session allocation retain supplied-record
suffixes on normal return. Existing finite collision search is reused. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Noise

theorem native_indexInsert (records : List HiddenRecord) (owner : IndexOwner) :
    NativeKeeps records (monadLift (indexInsert owner) : WG.M Nat) :=
  indexInsert_retains records owner

theorem generatePublic_retains (records : List HiddenRecord) (secret : Key) :
    NativeKeeps records (generatePublic secret) := by
  unfold generatePublic
  repeat' first
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_getKeypair
    | env_operation_fact native_setKeypair
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_modifyPeer
    | env_operation_fact native_peerDeref
    | env_operation_fact native_peerWord
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_and
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

theorem setChain_retains (records : List HiddenRecord) (pid : PeerId) (key hash : List UInt8) :
    NativeKeeps records ((noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid key hash) :=
  native_bind records _ _ (native_getPeer records pid) (fun _=>native_setPeer records _ _)

theorem keypairCreate_retains (records : List HiddenRecord) (peer : Option PeerId) :
    NativeKeeps records (keypairCreate peer) := by
  unfold keypairCreate
  repeat' first
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_getKeypair
    | env_operation_fact native_setKeypair
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_modifyPeer
    | env_operation_fact native_peerDeref
    | env_operation_fact native_peerWord
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_and
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

theorem addNewKeypair_retains (records : List HiddenRecord) (pid : PeerId) (key : KeypairId) :
    NativeKeeps records (addNewKeypair pid key) := by
  unfold addNewKeypair
  repeat' first
    | env_operation_fact keypairPut_retains
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_getKeypair
    | env_operation_fact native_setKeypair
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_modifyPeer
    | env_operation_fact native_peerDeref
    | env_operation_fact native_peerWord
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_and
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

theorem deriveKeys_retains (records : List HiddenRecord) (key : KeypairId)
    (initiator : Bool) (chainingKey : List UInt8) :
    NativeKeeps records (deriveKeys key initiator chainingKey) := by
  unfold deriveKeys
  repeat' first
    | env_operation_fact kdf_retains
    | env_operation_fact kdfOut_retains
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_getKeypair
    | env_operation_fact native_setKeypair
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_modifyPeer
    | env_operation_fact native_peerDeref
    | env_operation_fact native_peerWord
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_and
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

theorem indexReplaceHandshake_retains (records : List HiddenRecord) (pid : PeerId) (key : KeypairId) :
    NativeKeeps records (monadLift (indexReplaceHandshake pid key) : WG.M Bool) := by
  apply native_liftIndex
  intro table
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  dsimp [indexReplaceHandshake, indexHashed, branch, AmbientM.branch] at run
  split at run <;> cases run <;> exact pre

theorem createInitiation_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (createInitiation pid) := by
  unfold createInitiation
  repeat' first
    | env_operation_fact generatePublic_retains
    | env_operation_fact setChain_retains
    | env_operation_fact messageEphemeral_retains
    | env_operation_fact mixDh_retains
    | env_operation_fact mixPrecomputedDh_retains
    | env_operation_fact native_indexInsert
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_getKeypair
    | env_operation_fact native_setKeypair
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_modifyPeer
    | env_operation_fact native_peerDeref
    | env_operation_fact native_peerWord
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_and
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

theorem createResponse_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (createResponse pid) := by
  unfold createResponse
  repeat' first
    | env_operation_fact generatePublic_retains
    | env_operation_fact setChain_retains
    | env_operation_fact messageEphemeral_retains
    | env_operation_fact mixDh_retains
    | env_operation_fact kdf_retains
    | env_operation_fact kdfOut_retains
    | env_operation_fact native_indexInsert
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_getKeypair
    | env_operation_fact native_setKeypair
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_modifyPeer
    | env_operation_fact native_peerDeref
    | env_operation_fact native_peerWord
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_and
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

theorem addMacToPacket_retains (records : List HiddenRecord) (pid : PeerId) (message : List UInt8) :
    NativeKeeps records (addMacToPacket pid message) := by
  unfold addMacToPacket
  repeat' first
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_getKeypair
    | env_operation_fact native_setKeypair
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_modifyPeer
    | env_operation_fact native_peerDeref
    | env_operation_fact native_peerWord
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_and
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

theorem beginSession_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (beginSession pid) := by
  unfold beginSession handshakeZero
  repeat' first
    | env_operation_fact keypairCreate_retains
    | env_operation_fact addNewKeypair_retains
    | env_operation_fact deriveKeys_retains
    | env_operation_fact indexReplaceHandshake_retains
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact native_getKeypair
    | env_operation_fact native_setKeypair
    | env_operation_fact native_get
    | env_operation_fact native_modify
    | env_operation_fact native_modifyDev
    | env_operation_fact native_modifyPeer
    | env_operation_fact native_peerDeref
    | env_operation_fact native_peerWord
    | env_operation_fact native_hidden
    | env_operation_fact native_alloc
    | env_operation_fact native_clock
    | env_operation_fact native_expired
    | env_operation_fact native_and
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_invariant
    | env_operation_fact native_unsupported
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

end Leanux.Proofs.WG.Progress.RecordSuffix
