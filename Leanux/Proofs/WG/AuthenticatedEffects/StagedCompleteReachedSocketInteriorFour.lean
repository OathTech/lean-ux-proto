import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingPending

/-! The original lifetime-observed IPv4 route prefix, before the tunnel
append. Native guards, cache accesses and their event order are unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior.Four
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def socket4FinishFront (_e : Endpoint) (_bytes : List UInt8) (_ds : Nat)
    (_exactRx : Bool) (route : Option Route) : MixedM (Except Int Route) := do
  let some r := route | liftWGPrefix (invariant "send4 without a route")
  liftWGPrefix (liftRouting (Net.Fib.inSocketNs (Net.neighbourClassify r.dev)))
  return .ok r

def socket4RouteFront (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) : MixedM (Except Int Route) := do
  let mut route := fallback
  match rt with
  | .error err =>
    if ← liftWGPrefix (branch .send4RouteErr true) then return .error err
  | .ok r =>
    _ ← liftWGPrefix (branch .send4RouteErr false)
    if ← liftWGPrefix (branch .send4CacheSet cache.isSome) then dstCacheSetPrefix cache.get! r.src gen r.dev
    route := some r
  socket4FinishFront e bytes ds exactRx route

def socket4RetryFront (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) : MixedM (Except Int Route) := do
  let mut rt := rt
  let mismatch := srcIf != 0 && (match rt with
    | .error err => err == -EINVAL
    | .ok r => r.dev != srcIf)
  if ← liftWGPrefix (branch .send4SrcIfMismatch mismatch) then
    send4ClearSrcPrefix cache
    if ← liftWGPrefix (branch .send4ResetB cache.isSome) then dstCacheResetMixed cache.get!
    if ← liftWGPrefix (branch .send4PutRt (match rt with | .ok _ => true | .error _ => false)) then pure ()
    rt ← liftWGPrefix (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 0 e.addr)))
  socket4RouteFront e cache bytes ds exactRx gen fallback rt

def socket4MissFront (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) : MixedM (Except Int Route) := do
  let mut saddr := saddr
  let mut srcIf := srcIf
  let w ← liftWGPrefix (getRouting : WG.M Net.Routing)
  let confirmed := saddr == 0 || saddr == LOOPBACK4 || w.addrs4.contains saddr
  if ← liftWGPrefix (branch .send4SrcNotLocal !confirmed) then
    send4ClearSrcPrefix cache
    saddr := 0; srcIf := 0
    if ← liftWGPrefix (branch .send4ResetA cache.isSome) then dstCacheResetMixed cache.get!
  let rt ← liftWGPrefix (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 saddr e.addr)))
  socket4RetryFront e cache bytes ds exactRx gen fallback srcIf rt

def socket4AfterCacheFront (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) : MixedM (Except Int Route) := do
  if ← liftWGPrefix (branch .send4CacheMiss route.isNone) then
    socket4MissFront e cache bytes ds exactRx gen route saddr srcIf
  else socket4FinishFront e bytes ds exactRx route

def socket4Front (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) : MixedM (Except Int Route) := do
  let d ← liftWGPrefix getDev
  if ← liftWGPrefix (branch .send4SockNull d.sock4.isNone) then return .error (-ENONET)
  let gen := (← liftWGPrefix (liftRouting (Net.Fib.inSocketNs Net.Fib.getTable))).rtGenid4
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← liftWGPrefix (branch .send4HasCache cache.isSome) then
    let some pid := cache | liftWGPrefix (invariant "unreachable")
    if let some s ← dstCacheGetPrefix pid gen then
      route := some {dev := s.dev, src := s.src}; saddr := s.src
  socket4AfterCacheFront e cache bytes ds exactRx gen saddr e.srcIf route

def socketResult (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (result : Except Int Route) : MixedM Int := do
  match result with
  | .error err => pure err
  | .ok r => tunnelXmitPrefix e bytes ds r exactRx; pure 0

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem invariant_bind (s : String) (f : α → MixedM β) :
    ((liftWGPrefix (invariant s) : MixedM α) >>= f) = liftWGPrefix (invariant s) := rfl

theorem socket4FinishFront_factor (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) :
    send4FinishPrefix e bytes ds exactRx route = (socket4FinishFront e bytes ds exactRx route >>= socketResult e bytes ds exactRx) := by
  cases route <;> simp [send4FinishPrefix, socket4FinishFront, socketResult,
    invariant_bind]

theorem socket4RouteFront_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) :
    send4RouteDonePrefix e cache bytes ds exactRx gen fallback rt = (socket4RouteFront e cache bytes ds exactRx gen fallback rt >>= socketResult e bytes ds exactRx) := by
  cases rt <;> unfold send4RouteDonePrefix socket4RouteFront
  all_goals simp only [socket4FinishFront_factor]
  all_goals try simp only [bind_assoc, if_bind]
  repeat' first
    | rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all only [bind_assoc, if_bind, invariant_bind, pure_bind, ↓reduceIte, Option.some.injEq]; rfl)
  all_goals rfl

theorem socket4RetryFront_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (srcIf : Nat) (rt : Except Int Route) :
    send4RetryPrefix e cache bytes ds exactRx gen fallback srcIf rt = (socket4RetryFront e cache bytes ds exactRx gen fallback srcIf rt >>= socketResult e bytes ds exactRx) := by
  unfold send4RetryPrefix socket4RetryFront
  simp only [socket4RouteFront_factor]
  all_goals try simp only [bind_assoc, if_bind]
  repeat' first
    | rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all only [bind_assoc, if_bind, invariant_bind, pure_bind, ↓reduceIte, Option.some.injEq]; rfl)
  all_goals rfl

theorem socket4MissFront_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route)
    (saddr srcIf : Nat) :
    send4MissPrefix e cache bytes ds exactRx gen fallback saddr srcIf = (socket4MissFront e cache bytes ds exactRx gen fallback saddr srcIf >>= socketResult e bytes ds exactRx) := by
  unfold send4MissPrefix socket4MissFront
  simp only [socket4RetryFront_factor]
  all_goals try simp only [bind_assoc, if_bind]
  repeat' first
    | rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all only [bind_assoc, if_bind, invariant_bind, pure_bind, ↓reduceIte, Option.some.injEq]; rfl)
  all_goals rfl

theorem socket4AfterCacheFront_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) :
    send4AfterCachePrefix e cache bytes ds exactRx gen saddr srcIf route = (socket4AfterCacheFront e cache bytes ds exactRx gen saddr srcIf route >>= socketResult e bytes ds exactRx) := by
  unfold send4AfterCachePrefix socket4AfterCacheFront
  simp only [socket4FinishFront_factor, socket4MissFront_factor]
  all_goals try simp only [bind_assoc, if_bind]
  repeat' first
    | rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | (simp_all only [bind_assoc, if_bind, invariant_bind, pure_bind, ↓reduceIte, Option.some.injEq]; rfl)
  all_goals rfl

theorem socket4Front_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    send4Prefix e cache bytes ds exactRx =
      (socket4Front e cache bytes ds exactRx >>= socketResult e bytes ds exactRx) := by
  cases cache <;> unfold send4Prefix socket4Front
  all_goals simp only [socket4AfterCacheFront_factor,bind_assoc,if_bind,invariant_bind,pure_bind]
  all_goals repeat' first
    | with_reducible rfl
    | (socket_bind_head; with_reducible apply source_bind)
    | socket_factor_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split
  all_goals rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior.Four
