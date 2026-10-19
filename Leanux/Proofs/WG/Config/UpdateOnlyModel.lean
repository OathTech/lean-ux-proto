import Leanux.WG.Netlink
import Init.Data.UInt.Bitwise

/-! Validation refusals and flag algebra for the original peer command. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.UpdateOnly
open Leanux Leanux.WG

def validationError (attrs : PeerAttrs) : Option Int :=
  if attrs.publicKey.isNone then some (-EINVAL)
  else if attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL != 0 then some (-EOPNOTSUPP)
  else if attrs.protocolVersion.isSome && attrs.protocolVersion != some 1 then some (-EPFNOSUPPORT)
  else none

theorem masks (flags : UInt32) :
    ((flags ||| WGPEER_F_UPDATE_ONLY) &&& ~~~WGPEER_F_ALL = flags &&& ~~~WGPEER_F_ALL) ∧
    ((flags ||| WGPEER_F_UPDATE_ONLY) &&& WGPEER_F_REMOVE_ME = flags &&& WGPEER_F_REMOVE_ME) ∧
    ((flags ||| WGPEER_F_UPDATE_ONLY) &&& WGPEER_F_REPLACE_ALLOWEDIPS = flags &&& WGPEER_F_REPLACE_ALLOWEDIPS) := by
  constructor
  · apply UInt32.eq_of_toBitVec_eq
    simp [WGPEER_F_UPDATE_ONLY,WGPEER_F_ALL,BitVec.and_or_distrib_right]
  constructor
  · apply UInt32.eq_of_toBitVec_eq
    simp [WGPEER_F_UPDATE_ONLY,WGPEER_F_REMOVE_ME,BitVec.and_or_distrib_right]
  · apply UInt32.eq_of_toBitVec_eq
    simp [WGPEER_F_UPDATE_ONLY,WGPEER_F_REPLACE_ALLOWEDIPS,BitVec.and_or_distrib_right]

theorem blocks_creation (flags : UInt32) :
    (flags ||| WGPEER_F_UPDATE_ONLY) &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) ≠ 0 := by
  intro equal
  have bit := congrArg (fun x : UInt32=>x.toBitVec.getLsbD 2) equal
  simp [WGPEER_F_UPDATE_ONLY,WGPEER_F_REMOVE_ME] at bit

end Leanux.Proofs.WG.Config.UpdateOnly
