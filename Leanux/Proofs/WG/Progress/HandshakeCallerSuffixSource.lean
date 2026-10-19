import Leanux.Proofs.WG.Progress.HandshakeCreateSuffixSource
import Leanux.Proofs.WG.Progress.SocketSuffixSource
import Leanux.Proofs.WG.Progress.TimerHookSuffixSource
import Leanux.Proofs.WG.Progress.StagingSuffixSource
import Leanux.Proofs.WG.Progress.EndpointSuffixSource

/-! Actual complete handshake send and reception callers retain supplied
record suffixes on normal return, including every concrete protocol leaf. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem sendHandshakeResponse_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponse
  repeat' first
    | env_operation_fact createResponse_retains
    | env_operation_fact addMacToPacket_retains
    | env_operation_fact beginSession_retains
    | env_operation_fact timersDerived_retains
    | env_operation_fact timersTraversal_retains
    | env_operation_fact timersAnySent_retains
    | env_operation_fact sendBufferToPeer_retains
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
    | env_operation_step

theorem sendHandshakeInitiation_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiation
  repeat' first
    | env_operation_fact createInitiation_retains
    | env_operation_fact addMacToPacket_retains
    | env_operation_fact timersTraversal_retains
    | env_operation_fact timersAnySent_retains
    | env_operation_fact timersInitiated_retains
    | env_operation_fact sendBufferToPeer_retains
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
    | env_operation_step

theorem handshakeSendWorker_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (handshakeSendWorker pid) :=
  native_bind records _ _ (sendHandshakeInitiation_retains records pid)
    (fun _=>peerPut_retains records (some pid))

theorem makeCookie_retains (records : List HiddenRecord) (src : SkbSource) :
    NativeKeeps records (makeCookie src) := by
  unfold makeCookie
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
    | env_operation_step

theorem ratelimiterAllow_retains (records : List HiddenRecord) (src : SkbSource) :
    NativeKeeps records (ratelimiterAllow src) := by
  unfold ratelimiterAllow
  repeat' first
    | env_operation_fact native_clockInt
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
    | env_operation_step

theorem cookieValidatePacket_retains (records : List HiddenRecord) (message : List UInt8)
    (src : SkbSource) (checkCookie : Bool) :
    NativeKeeps records (cookieValidatePacket message src checkCookie) := by
  unfold cookieValidatePacket
  repeat' first
    | env_operation_fact makeCookie_retains
    | env_operation_fact ratelimiterAllow_retains
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
    | env_operation_step

theorem cookieMessageCreate_retains (records : List HiddenRecord) (index : Nat)
    (src : SkbSource) (mac : List UInt8) :
    NativeKeeps records (cookieMessageCreate index src mac) := by
  unfold cookieMessageCreate
  repeat' first
    | env_operation_fact makeCookie_retains
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
    | env_operation_step

theorem sendHandshakeCookie_retains (records : List HiddenRecord) (message : List UInt8) (src : SkbSource) :
    NativeKeeps records (sendHandshakeCookie message src) := by
  unfold sendHandshakeCookie
  repeat' first
    | env_operation_fact cookieMessageCreate_retains
    | env_operation_fact sendBufferAsReplyToSkb_retains
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
    | env_operation_step

theorem setPeerEndpointFromSkb_retains (records : List HiddenRecord) (pid : PeerId) (src : SkbSource) :
    NativeKeeps records (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  repeat' first
    | env_operation_fact endpointFromSkb_retains
    | env_operation_fact setPeerEndpoint_retains
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
    | env_operation_step

theorem receiveHandshakePacket_retains (records : List HiddenRecord) (message : List UInt8) (src : SkbSource) :
    NativeKeeps records (receiveHandshakePacket message src) := by
  unfold receiveHandshakePacket
  repeat' first
    | env_operation_fact cookieMessageConsume_retains
    | env_operation_fact cookieValidatePacket_retains
    | env_operation_fact sendHandshakeCookie_retains
    | env_operation_fact consumeInitiation_retains
    | env_operation_fact consumeResponse_retains
    | env_operation_fact setPeerEndpointFromSkb_retains
    | env_operation_fact sendHandshakeResponse_retains
    | env_operation_fact beginSession_retains
    | env_operation_fact timersDerived_retains
    | env_operation_fact timersComplete_retains
    | env_operation_fact keepalive_retains
    | env_operation_fact timersAnyReceived_retains
    | env_operation_fact timersTraversal_retains
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
    | env_operation_step

theorem receiveStep_retains (records : List HiddenRecord) :
    NativeKeeps records receiveStep := by
  unfold receiveStep
  repeat' first
    | env_operation_fact receiveHandshakePacket_retains
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
    | env_operation_step

end Leanux.Proofs.WG.Progress.RecordSuffix
