import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.TimerDiscipline.SendPeerFrames
import Leanux.Proofs.WG.Index.ReceiveOperations

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem receiveStats_tables (len : Nat) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄
      modifyDev (fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len })
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  mvcgen [modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals cases hd : (by assumption : World).k.wg <;>
    simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem receiveLoadThen_tables (next : Bool → M Unit)
    (body : ∀ b, ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ next b
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ receiveLoadThen next
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hh := hiddenClock64_kernel_spec TablesSafeKernel
  mvcgen [receiveLoadThen, birthdateTest, getDev, getK, branch, branchCmp, invariant, hh, body]

-- These receive-path operations leave the optional index table and cursor untouched.
theorem makeCookie_tables (src : SkbSource) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ makeCookie src
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hh := hidden_kernel_spec TablesSafeKernel
  have hc := hiddenClock64_kernel_spec TablesSafeKernel
  mvcgen [makeCookie, branchExpired, birthdateTest, getDev, getK, branch, branchCmp,
    invariant, modifyDev, modifyK, hh, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem ratelimiterAllow_tables (src : SkbSource) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ ratelimiterAllow src
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hh := hidden_kernel_spec TablesSafeKernel
  mvcgen [ratelimiterAllow, hiddenClock, envOk, getK, branch, branchCmp,
    invariant, unsupported, modifyK, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel]
  all_goals split <;> assumption

theorem cookieValidatePacket_tables (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ cookieValidatePacket msg src checkCookie
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hm := makeCookie_tables
  have hr := ratelimiterAllow_tables
  mvcgen [cookieValidatePacket, getDev, getK, branch, invariant, hm, hr]

theorem endpointFromSkb_tables (src : SkbSource) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ endpointFromSkb src
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  mvcgen [endpointFromSkb, branch, invariant, unsupported]

theorem dstCacheReset_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ dstCacheReset pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  have hh := hidden_kernel_spec TablesSafeKernel
  mvcgen [dstCacheReset, hiddenJiffies, getPeer, getDev, getK, invariant, unsupported, hp, hh]

theorem setPeerEndpointFromSkb_tables (pid : PeerId) (src : SkbSource) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ setPeerEndpointFromSkb pid src
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have he := endpointFromSkb_tables
  have hd := dstCacheReset_tables
  have hp := setPeer_tables
  mvcgen [setPeerEndpointFromSkb, setPeerEndpoint, requireNotPending, endpointEq,
    WG.andM, getPeer, getDev, getK, branch, invariant, he, hd, hp]

theorem timersHandshakeComplete_tables (pid : PeerId) (site : HiddenSite) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ timersHandshakeComplete pid site
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  have hh := hidden_kernel_spec TablesSafeKernel
  mvcgen [timersHandshakeComplete, delTimer, getPeer, getDev, getK, invariant, hp, hh]

theorem timersAnyAuthenticatedPacketReceived_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ timersAnyAuthenticatedPacketReceived pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  mvcgen [timersAnyAuthenticatedPacketReceived, delTimer, getPeer, getDev, getK, invariant, hp]

/-- The existing C2 socket spine exposes the table/cursor projection for any
optional peer observation, including the no-cache reply path. -/
theorem tunnelXmit_tables (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ TimerDiscipline.tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  have h := (ensures_iff _ _ _).mpr
    (TimerDiscipline.tunnelXmit_sendView 0 e bytes ds r exactRx
      (TimerDiscipline.sendAt w 0).1 (TimerDiscipline.sendAt w 0).2)
    w result final rfl run
  exact tablesSafe_of_cursor w.k final.k (congrArg Prod.fst h) pre

theorem send4_reply_tables (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ send4 e none bytes ds exactRx
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have ht := tunnelXmit_tables
  mvcgen [send4, routeLookup, getDev, getK, branch, invariant, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem send6_reply_tables (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ send6 e none bytes ds exactRx
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have ht := tunnelXmit_tables
  mvcgen [send6, routeLookup, getDev, getK, branch, invariant, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

/-- Reply-site variant of Noise.keypairAllocation_kernel_spec. -/
theorem keypairAllocation_kernel_spec_reply_variant (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ hiddenAlloc .replySkb ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hh := hidden_kernel_spec P
  noise_vcgen [hiddenAlloc,
    _private.Leanux.Kernel.Defs.«0».Leanux.allocRecord,
    _private.Leanux.Kernel.Defs.«0».Leanux.allocPlaceholder,
    invariant, unsupported, hh]
  case inv1 _ n _ _ _ _ _ _ => exact fun r _ => ⟨n-r.2+1⟩
  case inv2 => exact ((⇓? _ w => ⌜P w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try simp_all [WhileVariant.eval, SVal.evalsTo, SVal.uncurry,
    ExceptConds.true, ExceptConds.const]
  all_goals omega

theorem sendBufferAsReplyToSkb_tables (src : SkbSource) (buffer : List UInt8) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ sendBufferAsReplyToSkb src buffer
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have he := endpointFromSkb_tables
  have ha := keypairAllocation_kernel_spec_reply_variant TablesSafeKernel
  have h4 := send4_reply_tables
  have h6 := send6_reply_tables
  mvcgen [sendBufferAsReplyToSkb, branch, invariant, he, ha, h4, h6]

theorem cookieMessageCreate_tables (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ cookieMessageCreate index src mac1
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hh := hidden_kernel_spec TablesSafeKernel
  have hm := makeCookie_tables
  mvcgen [cookieMessageCreate, getDev, getK, invariant, hh, hm]

theorem sendHandshakeCookie_tables (msg : List UInt8) (src : SkbSource) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ sendHandshakeCookie msg src
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hc := cookieMessageCreate_tables
  have hs := sendBufferAsReplyToSkb_tables
  mvcgen [sendHandshakeCookie, hc, hs]

end Leanux.Proofs.WG.Index
