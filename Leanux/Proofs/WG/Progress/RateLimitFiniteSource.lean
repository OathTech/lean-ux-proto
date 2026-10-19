import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.WG.Receive

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- The original token-bucket body with its actual allocation encounter
replaced by the unconditional finite allocation evaluator. -/
def ratelimiter (src : SkbSource) : WG.M Bool := do
  let (v6, ip) ← do
    if ← branch .rlProtoIp (src.family == 4) then pure (false, src.saddr)
    else if ← branch .rlProtoIp6 (src.family == 6) then pure (true, src.saddr / 2 ^ 64)
    else invariant "a handshake skb that is neither IPv4 nor IPv6 at the ratelimiter"
  let table (k : WGWorld) : List (Nat × Int × Int) := if v6 then k.ratelimiter.table6 else k.ratelimiter.table
  let setTable (k : WGWorld) (t : List (Nat × Int × Int)) : WGWorld :=
    if v6 then { k with ratelimiter := { k.ratelimiter with table6 := t } }
    else { k with ratelimiter := { k.ratelimiter with table := t } }
  match (table (← get)).find? (·.1 == ip) with
  | some (_, tokens, lastTime) =>
    _ ← branch .rlEntryMatch true
    let now ← hiddenClock .ratelimiterNow
    let newTokens := min TOKEN_MAX (tokens + now - lastTime)
    let ret ← branchCmp .rlAllow (newTokens ≥ PACKET_COST) newTokens PACKET_COST
    let tokens' := if ret then newTokens - PACKET_COST else newTokens
    modify fun k => setTable k ((table k).map fun e => if e.1 == ip then (ip, tokens', now) else e)
    return ret
  | none =>
    let k ← get
    let total := k.ratelimiter.table.length + k.ratelimiter.table6.length + 1
    if ← branchCmp .rlOverLimit (total > RL_MAX_ENTRIES) (Int.ofNat total) (Int.ofNat RL_MAX_ENTRIES) then
      unsupported "the ratelimiter table limit (16384 distinct source IPs — out of reach)"
    if ← branch .rlAllocFail !(← monadLift (hiddenAllocFinite .kmemCacheAllocRlEntry)) then
      return false
    let now ← hiddenClock .ratelimiterInsertNow
    modify fun k => setTable k ((ip, TOKEN_MAX - PACKET_COST, now) :: table k)
    return true

/-- The original MAC/cookie checks with the exact finite rate limiter. -/
def validateCookie (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) : WG.M MacState := do
  let len := msg.length
  let computed := blake2s 16 (← getDev).mac1Key (msg.take (len - 32))
  let mac1 := (msg.drop (len - 32)).take 16
  if ← branch .macInvalid (computed != mac1) then return .invalid
  if ← branch .macNoCookieCheck (!checkCookie) then return .noCookie
  let cookie ← makeCookie src
  let computed2 := blake2s 16 cookie (msg.take (len - 16))
  let givenMac2 := (msg.drop (len - 16)).take 16
  if ← branch .macCookieInvalid (computed2 != givenMac2) then return .noCookie
  if ← branch .macRatelimited !(← ratelimiter src) then return .ratelimited
  return .withCookie

theorem ratelimiter_source (src : SkbSource) :
    WG.ratelimiterAllow src = ratelimiter src := by
  unfold WG.ratelimiterAllow ratelimiter
  have allocation : (hiddenAlloc .kmemCacheAllocRlEntry : WG.M Bool) =
      monadLift (hiddenAllocFinite .kmemCacheAllocRlEntry) := by
    change monadLift (AmbientM.hiddenAlloc .kmemCacheAllocRlEntry) = _
    rw [hiddenAlloc_finite_source]
  rw [allocation]
  rfl

theorem validateCookie_source (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    WG.cookieValidatePacket msg src checkCookie = validateCookie msg src checkCookie := by
  unfold WG.cookieValidatePacket validateCookie
  rw [ratelimiter_source]

end Leanux.Proofs.WG.Progress.HandshakeFinite
