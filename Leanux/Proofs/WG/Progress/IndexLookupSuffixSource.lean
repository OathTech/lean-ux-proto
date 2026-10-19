import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Progress.RxPrimitiveSuffixSource
import Leanux.Proofs.WG.Progress.AllowedLookupSuffixSource

/-! Actual owner and lookup operations preserve the supplied-record suffix.
The embedded peer-word store and reference acquisition remain in source order. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem indexBucket_retains (records : List HiddenRecord) (index : Nat) :
    NativeKeeps records (liftIndex (indexBucket index)) := by
  apply native_liftIndex
  intro table
  exact preserves_pure _

theorem setPeerWord_retains (records : List HiddenRecord) (owner : IndexOwner) (peer : Option PeerId) :
    NativeKeeps records (owner.setPeerWord peer) := by
  cases owner <;> unfold IndexOwner.setPeerWord
  · exact native_bind records _ _ (native_getPeer records _) (fun _=>native_setPeer records _ _)
  · exact native_bind records _ _ (native_getKeypair records _) (fun _=>native_setKeypair records _ _)

theorem indexLookup_retains (records : List HiddenRecord) (kinds : List IndexKind) (index : Nat) :
    NativeKeeps records (indexLookup kinds index) := by
  unfold indexLookup
  apply native_bind records _ _ (indexBucket_retains records index)
  intro bucket
  apply native_bind records
  · apply native_forIn records
    intro entry pair
    repeat' first
      | env_operation_fact native_branch
      | env_operation_fact native_pure
      | env_operation_fact native_bind
      | split
      | env_operation_step
  · intro pair
    repeat' first
      | env_operation_fact indexBucket_retains
      | env_operation_fact native_peerWord
      | env_operation_fact peerGetMaybeZero_retains
      | env_operation_fact setPeerWord_retains
      | env_operation_fact native_branch
      | env_operation_fact native_invariant
      | env_operation_fact native_pure
      | env_operation_fact native_forIn
      | env_operation_fact native_bind
      | split
      | env_operation_step

theorem pubkeyLookup_retains (records : List HiddenRecord) (key : Key) :
    NativeKeeps records (pubkeyLookup key) := by
  unfold pubkeyLookup
  exact native_bind records _ _ (native_getDev records) (fun _=>
    native_bind records _ _ (native_branch records _ _) (fun _=>peerGetMaybeZero_retains records _))

end Leanux.Proofs.WG.Progress.RecordSuffix
