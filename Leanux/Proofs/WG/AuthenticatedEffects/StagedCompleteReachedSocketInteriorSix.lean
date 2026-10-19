import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorFour

/-! Exact observed IPv6 cache and route stages before the tunnel append. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior.Six
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def clear (cache : Option PeerId) : MixedM Unit := do
  if let some pid := cache then
    modifyPeerKeysPrefix pid fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0}}

def finish (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (route : Option Route) : MixedM Int := do
  let some r := route | liftWGPrefix (invariant "send6 without a route")
  tunnelXmitPrefix e bytes ds r exactRx
  return 0

def routeDone (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (rt : Except Int Route) : MixedM Int := do
  let mut route := fallback
  match rt with
  | .error err =>
    if ← liftWGPrefix (branch .send6RouteErr true) then return err
  | .ok r =>
    _ ← liftWGPrefix (branch .send6RouteErr false)
    if ← liftWGPrefix (branch .send6CacheSet cache.isSome) then dstCacheSetPrefix cache.get! r.src gen r.dev
    route := some r
  finish e bytes ds exactRx route

def miss (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (saddr : Nat) : MixedM Int := do
  let mut saddr := saddr
  let w ← liftWGPrefix (getRouting : WG.M Net.Routing)
  let notLocal := saddr != 0 && !(saddr == 1 || saddr == LO_LINK_LOCAL || w.addrs6.contains saddr)
  if ← liftWGPrefix (branch .send6SrcNotLocal notLocal) then
    clear cache
    saddr := 0
    if ← liftWGPrefix (branch .send6Reset cache.isSome) then dstCacheResetMixed cache.get!
  let rt ← liftWGPrefix (liftRouting (Net.routeLookup 6 saddr e.addr))
  routeDone e cache bytes ds exactRx gen fallback rt

def afterCache (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen saddr : Nat) (route : Option Route) : MixedM Int := do
  if ← liftWGPrefix (branch .send6CacheMiss route.isNone) then
    miss e cache bytes ds exactRx gen route saddr
  else finish e bytes ds exactRx route

def source (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) : MixedM Int := do
  let d ← liftWGPrefix getDev
  if ← liftWGPrefix (branch .send6SockNull d.sock6.isNone) then return -ENONET
  let gen := (← liftWGPrefix (getRouting : WG.M Net.Routing)).ipv6Gen
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← liftWGPrefix (branch .send6HasCache cache.isSome) then
    let some pid := cache | liftWGPrefix (invariant "unreachable")
    if let some s ← dstCacheGetPrefix pid gen then
      route := some {dev := s.dev,src := s.src}; saddr := s.src
  afterCache e cache bytes ds exactRx gen saddr route

def finishFront (route : Option Route) : MixedM (Except Int Route) := do
  let some r := route | liftWGPrefix (invariant "send6 without a route")
  return .ok r

def routeFront (cache : Option PeerId) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) : MixedM (Except Int Route) := do
  let mut route := fallback
  match rt with
  | .error err =>
    if ← liftWGPrefix (branch .send6RouteErr true) then return .error err
  | .ok r =>
    _ ← liftWGPrefix (branch .send6RouteErr false)
    if ← liftWGPrefix (branch .send6CacheSet cache.isSome) then dstCacheSetPrefix cache.get! r.src gen r.dev
    route := some r
  finishFront route

def missFront (e : Endpoint) (cache : Option PeerId) (gen : Nat) (fallback : Option Route)
    (saddr : Nat) : MixedM (Except Int Route) := do
  let mut saddr := saddr
  let w ← liftWGPrefix (getRouting : WG.M Net.Routing)
  let notLocal := saddr != 0 && !(saddr == 1 || saddr == LO_LINK_LOCAL || w.addrs6.contains saddr)
  if ← liftWGPrefix (branch .send6SrcNotLocal notLocal) then
    clear cache
    saddr := 0
    if ← liftWGPrefix (branch .send6Reset cache.isSome) then dstCacheResetMixed cache.get!
  let rt ← liftWGPrefix (liftRouting (Net.routeLookup 6 saddr e.addr))
  routeFront cache gen fallback rt

def afterCacheFront (e : Endpoint) (cache : Option PeerId) (gen saddr : Nat)
    (route : Option Route) : MixedM (Except Int Route) := do
  if ← liftWGPrefix (branch .send6CacheMiss route.isNone) then missFront e cache gen route saddr
  else finishFront route

def front (e : Endpoint) (cache : Option PeerId) : MixedM (Except Int Route) := do
  let d ← liftWGPrefix getDev
  if ← liftWGPrefix (branch .send6SockNull d.sock6.isNone) then return .error (-ENONET)
  let gen := (← liftWGPrefix (getRouting : WG.M Net.Routing)).ipv6Gen
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← liftWGPrefix (branch .send6HasCache cache.isSome) then
    let some pid := cache | liftWGPrefix (invariant "unreachable")
    if let some s ← dstCacheGetPrefix pid gen then
      route := some {dev := s.dev,src := s.src}; saddr := s.src
  afterCacheFront e cache gen saddr route

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem invariant_bind (s : String) (f : α → MixedM β) :
    ((liftWGPrefix (invariant s) : MixedM α) >>= f) = liftWGPrefix (invariant s) := rfl


theorem source_eq (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    source e cache bytes ds exactRx = send6Prefix e cache bytes ds exactRx := by
  cases cache <;> unfold source send6Prefix afterCache miss routeDone finish clear modifyPeerKeysPrefix
  all_goals repeat' first
    | with_reducible rfl
    | simp +failIfUnchanged only [Bool.false_eq_true,↓reduceIte,Option.isSome_some,Option.isSome_none,Option.isNone_none,Option.isNone_some]
    | simp +failIfUnchanged only [bind_assoc,pure_bind,invariant_bind]
    | with_reducible apply source_bind
    | cached6_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem finish_factor (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) (route : Option Route) :
    finish e bytes ds exactRx route = (finishFront route >>= Four.socketResult e bytes ds exactRx) := by
  cases route <;> simp [finish,finishFront,Four.socketResult,invariant_bind]

theorem route_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (rt : Except Int Route) :
    routeDone e cache bytes ds exactRx gen fallback rt =
      (routeFront cache gen fallback rt >>= Four.socketResult e bytes ds exactRx) := by
  cases rt <;> unfold routeDone routeFront
  all_goals simp only [finish_factor,bind_assoc,if_bind]
  repeat' first
    | with_reducible rfl
    | simp +failIfUnchanged only [Bool.false_eq_true,↓reduceIte,Option.isSome_some,Option.isSome_none,Option.isNone_none,Option.isNone_some]
    | simp +failIfUnchanged only [pure_bind]
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all only [bind_assoc,if_bind,invariant_bind,pure_bind,↓reduceIte]; rfl)
  all_goals rfl

theorem miss_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (saddr : Nat) :
    miss e cache bytes ds exactRx gen fallback saddr =
      (missFront e cache gen fallback saddr >>= Four.socketResult e bytes ds exactRx) := by
  unfold miss missFront
  simp only [route_factor,bind_assoc,if_bind]
  repeat' first
    | with_reducible rfl
    | simp +failIfUnchanged only [Bool.false_eq_true,↓reduceIte,Option.isSome_some,Option.isSome_none,Option.isNone_none,Option.isNone_some]
    | simp +failIfUnchanged only [bind_assoc,if_bind,pure_bind,invariant_bind]
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all only [bind_assoc,if_bind,invariant_bind,pure_bind,↓reduceIte]; rfl)
  all_goals rfl

theorem afterCache_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen saddr : Nat) (route : Option Route) :
    afterCache e cache bytes ds exactRx gen saddr route =
      (afterCacheFront e cache gen saddr route >>= Four.socketResult e bytes ds exactRx) := by
  unfold afterCache afterCacheFront
  simp only [finish_factor,miss_factor,bind_assoc,if_bind]
  repeat' first
    | with_reducible rfl
    | simp +failIfUnchanged only [Bool.false_eq_true,↓reduceIte,Option.isSome_some,Option.isSome_none,Option.isNone_none,Option.isNone_some]
    | simp +failIfUnchanged only [bind_assoc,if_bind,pure_bind,invariant_bind]
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all only [bind_assoc,if_bind,invariant_bind,pure_bind,↓reduceIte]; rfl)
  all_goals rfl

theorem source_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) : source e cache bytes ds exactRx = (front e cache >>= Four.socketResult e bytes ds exactRx) := by
  unfold source front
  simp only [afterCache_factor,bind_assoc,if_bind]
  repeat' first
    | with_reducible rfl
    | simp +failIfUnchanged only [Bool.false_eq_true,↓reduceIte,Option.isSome_some,Option.isSome_none,Option.isNone_none,Option.isNone_some]
    | simp +failIfUnchanged only [bind_assoc,pure_bind,invariant_bind]
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all only [bind_assoc,if_bind,invariant_bind,pure_bind,↓reduceIte]; rfl)
  all_goals rfl

/-- Exact original IPv6 socket factoring for both cached transport and uncached
replies. The result retains every native early return and Stop before emission. -/

theorem socket6Front_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    send6Prefix e cache bytes ds exactRx =
      (front e cache >>= Four.socketResult e bytes ds exactRx) := by
  rw [← source_eq,source_factor]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior.Six
