import Leanux.Proofs.WG.AuthenticatedEffects.Emission

/-! Invalid MAC1 drops before cookie construction or Noise processing,
independently of load and handshake message type. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.WG.Cookies Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.Framing

def invalidDropEntry (loaded : Bool) (a : Ambient) : Ambient :=
  if loaded then dropEntry a else
    record (record (record (record a .hsLoadedOperand false) .hsNotLoaded true)
      .hsMacNoCookie false) .hsNeedsCookieLoaded false

theorem afterMac_invalid_any (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (loaded : Bool) :
    ((afterMac msg src loaded .invalid).run w).run a =
      .ok (((),w),invalidDropEntry loaded a) := by
  cases loaded with
  | true => exact afterMac_invalid msg src w a
  | false =>
    have hc : (MacState.invalid == MacState.withCookie) = false := rfl
    have hn : (MacState.invalid == MacState.noCookie) = false := rfl
    simp [afterMac,hc,hn,WG.orM,WG.andM,StateT.run_bind,branch,branch_run,invalidDropEntry]

theorem cookieValidate_invalid (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w : WGWorld) (a : Ambient) (d : Device)
    (hd : w.dev = some d) (bad : mac1Computed d msg ≠ mac1Given msg) :
    ((cookieValidatePacket msg src loaded).run w).run a =
      .ok ((.invalid,w),record a .macInvalid true) := by
  have hg (ambient : Ambient) : (getDev.run w).run ambient = .ok ((d,w),ambient) := by
    simp [getDev,hd]
  have hb : (blake2s 16 d.mac1Key (msg.take (msg.length - 32)) !=
      (msg.drop (msg.length - 32)).take 16) = true := by
    simpa only [bne_iff_ne,mac1Computed,mac1Given] using bad
  have bad' := bad
  simp only [mac1Computed,mac1Given] at bad'
  simp [cookieValidatePacket,StateT.run_bind,hg,branch,branch_run,hb,bad']

theorem receive_bad_mac1_any (msg : List UInt8) (src : SkbSource)
    (w u : WGWorld) (a b : Ambient) (d : Device) (loaded : Bool)
    (notCookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE)
    (load : (loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (hd : u.dev = some d) (bad : mac1Computed d msg ≠ mac1Given msg) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),u),invalidDropEntry loaded (record b .macInvalid true)) := by
  have kind : (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = false := by simpa using notCookie
  rw [receive_factor]
  simp only [StateT.run_bind,kind,branch,StateT.run_monadLift,StateT.run_pure,
    monadLift_self,branch_run,except_ok_bind,pure_bind,Bool.false_eq_true,↓reduceIte,
    load,cookieValidate_invalid msg src loaded u b d hd bad]
  exact afterMac_invalid_any msg src u (record b .macInvalid true) loaded

theorem receive_bad_mac1_no_send (msg : List UInt8) (src : SkbSource)
    (w u v : WGWorld) (a b c : Ambient) (d : Device) (loaded : Bool)
    (notCookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE)
    (load : (loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (hd : u.dev = some d) (bad : mac1Computed d msg ≠ mac1Given msg)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),c)) :
    v.sent = w.sent := by
  rw [receive_bad_mac1_any msg src w u a b d loaded notCookie load hd bad] at run
  cases run
  exact (ProjectedAction.iff_run_ambient _ _ _).mp loadPhase_sent w _ loaded u b load

end Leanux.Proofs.WG.AuthenticatedEffects
