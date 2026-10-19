import Leanux.Proofs.WG.Progress.NoisePrimitiveSuffixSource
import Leanux.Proofs.WG.Progress.IndexLookupSuffixSource

/-! Complete original handshake and cookie consumers retain supplied-record
suffixes on normal return, with actual lookup/reference and crypto leaves. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing


theorem native_ite {α : Type} (records : List HiddenRecord) (p : Prop)
    [Decidable p] (yes no : WG.M α)
    (hy : NativeKeeps records yes) (hn : NativeKeeps records no) :
    NativeKeeps records (if p then yes else no) := by
  by_cases h : p
  · simpa only [ite_eq_left h] using hy
  · simpa only [ite_eq_right h] using hn

theorem native_dite {α : Type} (records : List HiddenRecord) (p : Prop)
    [Decidable p] (yes : p → WG.M α) (no : ¬p → WG.M α)
    (hy : ∀ h, NativeKeeps records (yes h)) (hn : ∀ h, NativeKeeps records (no h)) :
    NativeKeeps records (if h : p then yes h else no h) := by
  by_cases h : p
  · simpa only [dite_eq_left h] using hy h
  · simpa only [dite_eq_right h] using hn h

theorem consumeInitiation_retains (records : List HiddenRecord) (message : List UInt8) :
    NativeKeeps records (consumeInitiation message) := by
  unfold consumeInitiation
  repeat' first
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact peerPut_retains
    | env_operation_fact pubkeyLookup_retains
    | env_operation_fact messageEphemeral_retains
    | env_operation_fact mixDh_retains
    | env_operation_fact mixPrecomputedDh_retains
    | env_operation_fact messageDecrypt_retains
    | env_operation_fact native_clock
    | env_operation_fact native_branch
    | env_operation_fact native_branchCmp
    | env_operation_fact native_or
    | env_operation_fact native_invariant
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

theorem consumeResponse_retains (records : List HiddenRecord) (message : List UInt8) :
    NativeKeeps records (consumeResponse message) := by
  unfold consumeResponse
  repeat' first
    | env_operation_fact native_getDev
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact peerPut_retains
    | env_operation_fact indexLookup_retains
    | env_operation_fact messageEphemeral_retains
    | env_operation_fact mixDh_retains
    | env_operation_fact kdf_retains
    | env_operation_fact kdfOut_retains
    | env_operation_fact messageDecrypt_retains
    | env_operation_fact native_branch
    | env_operation_fact native_invariant
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

theorem cookieMessageConsume_retains (records : List HiddenRecord) (message : List UInt8) :
    NativeKeeps records (cookieMessageConsume message) := by
  unfold cookieMessageConsume
  repeat' first
    | env_operation_fact native_getPeer
    | env_operation_fact native_setPeer
    | env_operation_fact peerPut_retains
    | env_operation_fact indexLookup_retains
    | env_operation_fact native_clock
    | env_operation_fact native_branch
    | env_operation_fact native_invariant
    | env_operation_fact native_pure
    | env_operation_fact native_bind
    | env_operation_fact native_ite
    | env_operation_fact native_dite
    | env_operation_step

end Leanux.Proofs.WG.Progress.RecordSuffix
