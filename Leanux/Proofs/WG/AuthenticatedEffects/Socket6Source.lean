import Leanux.Proofs.WG.AuthenticatedEffects.Socket4Source

/-! The IPv6 reply prefix retains every original route/allocation guard. -/
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes

def socket6Front (e : Endpoint) (cache : Option PeerId) : WG.M (Except Int Route) := do
  let d ← getDev
  if ← branch .send6SockNull d.sock6.isNone then return .error (-ENONET)
  let gen := (← getRouting).ipv6Gen
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← branch .send6HasCache cache.isSome then
    let some pid := cache | invariant "unreachable"
    if let some s ← dstCacheGet pid gen then
      route := some { dev := s.dev, src := s.src }; saddr := s.src
  if ← branch .send6CacheMiss route.isNone then
    -- !ipv6_addr_any(saddr) && !ipv6_chk_addr(net, saddr, NULL, 0)
    let w ← getRouting
    let notLocal := saddr != 0 && !(saddr == 1 || saddr == LO_LINK_LOCAL || w.addrs6.contains saddr)   -- W5: the link-local address on lo
    if ← branch .send6SrcNotLocal notLocal then
      if let some pid := cache then
        let p ← getPeer pid
        setPeer pid { p with endpoint := p.endpoint.map fun e => { e with src := 0 } }
      saddr := 0
      if ← branch .send6Reset cache.isSome then dstCacheReset cache.get!
    match ← Net.routeLookup 6 saddr e.addr with
    | .error err =>
      if ← branch .send6RouteErr true then return .error err
    | .ok r =>
      _ ← branch .send6RouteErr false
      if ← branch .send6CacheSet cache.isSome then dstCacheSet cache.get! r.src gen r.dev
      route := some r
  let some r := route | invariant "send6 without a route"
  return .ok r

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem invariant_bind (s : String) (f : α → WG.M β) :
    ((invariant s : WG.M α) >>= f) = invariant s := rfl

theorem socket6_factor (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    send6 e none bytes ds exactRx = (do
      match ← socket6Front e none with
      | .error err => pure err
      | .ok r => tunnelXmitSource e bytes ds r exactRx; pure 0) := by
  unfold send6 socket6Front
  simp only [Option.isSome_none, Option.isNone_none]
  simp only [bind_assoc, if_bind, invariant_bind]
  repeat' first
    | rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all only [bind_assoc, if_bind, pure_bind, ↓reduceIte]; rfl)
  all_goals simp_all [bind_assoc, invariant_bind]
  all_goals repeat' first
    | rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all [bind_assoc, if_bind, invariant_bind]; rfl)
  all_goals rfl

end Leanux.Proofs.WG.AuthenticatedEffects
