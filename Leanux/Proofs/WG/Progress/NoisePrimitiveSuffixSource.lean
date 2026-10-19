import Leanux.Proofs.WG.Progress.RxPrimitiveSuffixSource
import Leanux.WG.Handshake

/-! Normal supplied-record suffix transport through the original Noise
cryptographic helper calls. Pure byte computations are left untouched. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG

theorem kdf_retains (records : List HiddenRecord) (second third : Bool)
    (key data : List UInt8) : NativeKeeps records (kdf second third key data) := by
  unfold kdf
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_pure records _
    | with_reducible apply native_or records
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem kdfOut_retains (records : List HiddenRecord) (outputs : List (List UInt8)) (index : Nat) :
    NativeKeeps records (kdfOut outputs index) := by
  unfold kdfOut
  split
  · exact native_pure records _
  · exact native_invariant records _

theorem messageEphemeral_retains (records : List HiddenRecord) (copy : Bool)
    (ephemeral key hash : List UInt8) :
    NativeKeeps records (messageEphemeral copy ephemeral key hash) := by
  unfold messageEphemeral
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact kdf_retains records _ _ _ _
    | with_reducible exact kdfOut_retains records _ _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | (with_reducible intro x; try dsimp only)

theorem mixDh_retains (records : List HiddenRecord) (needKey : Bool)
    (key privateKey publicKey : List UInt8) :
    NativeKeeps records (mixDh needKey key privateKey publicKey) := by
  unfold mixDh
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact kdf_retains records _ _ _ _
    | with_reducible exact kdfOut_retains records _ _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem mixPrecomputedDh_retains (records : List HiddenRecord) (key shared : List UInt8) :
    NativeKeeps records (mixPrecomputedDh key shared) := by
  unfold mixPrecomputedDh
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact kdf_retains records _ _ _ _
    | with_reducible exact kdfOut_retains records _ _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

theorem messageDecrypt_retains (records : List HiddenRecord) (sealed key hash : List UInt8) :
    NativeKeeps records (messageDecrypt sealed key hash) := by
  unfold messageDecrypt
  repeat' first
    | with_reducible exact native_branch records _ _
    | with_reducible exact native_invariant records _
    | with_reducible exact native_pure records _
    | with_reducible apply native_bind records
    | split
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Progress.RecordSuffix
