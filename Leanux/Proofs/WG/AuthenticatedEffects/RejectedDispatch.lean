import Leanux.Proofs.WG.AuthenticatedEffects.InvalidMac

/-! A Noise refusal returns before the receive path's endpoint, response,
session, timer and receive-accounting suffix. The consumer's own cleanup
remains visible in its native run; no arbitrary-state restoration is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.WG.Cookies Leanux.Proofs.WG.CounterWindow

def authenticatedMac (loaded : Bool) : MacState := if loaded then .withCookie else .noCookie

def proceedEntry (loaded : Bool) (a : Ambient) : Ambient :=
  if loaded then record (record a .hsLoadedOperand true) .hsLoadedCookieOk true
  else record (record (record a .hsLoadedOperand false) .hsNotLoaded true) .hsMacNoCookie true

def initiationConsumerEntry (loaded : Bool) (a : Ambient) : Ambient :=
  record (record (proceedEntry loaded a) .hsSwitchInitiation true) .hsInitNeedsCookie false

def responseConsumerEntry (loaded : Bool) (a : Ambient) : Ambient :=
  record (record (record (proceedEntry loaded a) .hsSwitchInitiation false)
    .hsSwitchResponse true) .hsRespNeedsCookie false

theorem afterMac_initiation_refused (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (run : ((consumeInitiation msg).run w).run (initiationConsumerEntry loaded a) =
      .ok ((none,v),b)) :
    ((afterMac msg src loaded (authenticatedMac loaded)).run w).run a =
      .ok (((),v),record b .hsInitNoPeer true) := by
  have noCookie : (MacState.noCookie == MacState.noCookie) = true := rfl
  have withCookie : (MacState.withCookie == MacState.withCookie) = true := rfl
  cases loaded <;>
    simp [afterMac,authenticatedMac,kind,noCookie,withCookie,WG.orM,WG.andM,StateT.run_bind,branch,
      branch_run,initiationConsumerEntry,proceedEntry] at run ⊢ <;> rw [run] <;> rfl

theorem afterMac_response_refused (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (run : ((consumeResponse msg).run w).run (responseConsumerEntry loaded a) =
      .ok ((none,v),b)) :
    ((afterMac msg src loaded (authenticatedMac loaded)).run w).run a =
      .ok (((),v),record b .hsRespNoPeer true) := by
  have noCookie : (MacState.noCookie == MacState.noCookie) = true := rfl
  have withCookie : (MacState.withCookie == MacState.withCookie) = true := rfl
  cases loaded <;>
    simp [afterMac,authenticatedMac,kind,noCookie,withCookie,MESSAGE_HANDSHAKE_RESPONSE,MESSAGE_HANDSHAKE_INITIATION,
      WG.orM,WG.andM,StateT.run_bind,branch,branch_run,responseConsumerEntry,proceedEntry]
      at run ⊢ <;> rw [run] <;> rfl

theorem receive_initiation_refused (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (load : (loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeInitiation msg).run q).run (initiationConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),record d .hsInitNoPeer true) := by
  rw [receive_factor]
  have notCookie : (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = false := by
    simp only [kind,MESSAGE_HANDSHAKE_INITIATION,MESSAGE_HANDSHAKE_COOKIE]
    rfl
  simp only [StateT.run_bind,notCookie,branch,StateT.run_monadLift,StateT.run_pure,
    monadLift_self,branch_run,except_ok_bind,pure_bind,Bool.false_eq_true,↓reduceIte,load,mac]
  exact afterMac_initiation_refused msg src loaded q v c d kind refused

theorem receive_response_refused (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (load : (loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeResponse msg).run q).run (responseConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),record d .hsRespNoPeer true) := by
  rw [receive_factor]
  have notCookie : (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = false := by
    simp only [kind,MESSAGE_HANDSHAKE_RESPONSE,MESSAGE_HANDSHAKE_COOKIE]
    rfl
  simp only [StateT.run_bind,notCookie,branch,StateT.run_monadLift,StateT.run_pure,
    monadLift_self,branch_run,except_ok_bind,pure_bind,Bool.false_eq_true,↓reduceIte,load,mac]
  exact afterMac_response_refused msg src loaded q v c d kind refused

end Leanux.Proofs.WG.AuthenticatedEffects
