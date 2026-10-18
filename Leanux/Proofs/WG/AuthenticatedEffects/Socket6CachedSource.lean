import Leanux.Proofs.WG.AuthenticatedEffects.Socket6Source

/-! Cached IPv6 source stages isolate route acquisition from the actual sole
socket append. Native cache hit/miss, invalid source and error fallthroughs
remain in their original order; no endpoint or route premise is imposed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.Socket6Cached
open Leanux Leanux.WG Lifetimes
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option pp.structureInstances false

def clear (cache : Option PeerId) : WG.M Unit := do
  if let some pid := cache then
    let p ← getPeer pid
    setPeer pid {p with endpoint := p.endpoint.map fun e => {e with src := 0}}

def finish (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)
    (route : Option Route) : WG.M Int := do
  let some r := route | invariant "send6 without a route"
  (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx
  return 0

def routeDone (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (rt : Except Int Route) : WG.M Int := do
  let mut route := fallback
  match rt with
  | .error err =>
    if ← branch .send6RouteErr true then return err
  | .ok r =>
    _ ← branch .send6RouteErr false
    if ← branch .send6CacheSet cache.isSome then dstCacheSet cache.get! r.src gen r.dev
    route := some r
  finish e bytes ds exactRx route

def miss (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (saddr : Nat) : WG.M Int := do
  let mut saddr := saddr
  let w ← getRouting
  let notLocal := saddr != 0 && !(saddr == 1 || saddr == LO_LINK_LOCAL || w.addrs6.contains saddr)
  if ← branch .send6SrcNotLocal notLocal then
    clear cache
    saddr := 0
    if ← branch .send6Reset cache.isSome then dstCacheReset cache.get!
  let rt ← Net.routeLookup 6 saddr e.addr
  routeDone e cache bytes ds exactRx gen fallback rt

def afterCache (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen saddr : Nat) (route : Option Route) : WG.M Int := do
  if ← branch .send6CacheMiss route.isNone then
    miss e cache bytes ds exactRx gen route saddr
  else finish e bytes ds exactRx route

def source (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) : WG.M Int := do
  let d ← getDev
  if ← branch .send6SockNull d.sock6.isNone then return -ENONET
  let gen := (← getRouting).ipv6Gen
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← branch .send6HasCache cache.isSome then
    let some pid := cache | invariant "unreachable"
    if let some s ← dstCacheGet pid gen then
      route := some {dev := s.dev,src := s.src}; saddr := s.src
  afterCache e cache bytes ds exactRx gen saddr route

def finishFront (route : Option Route) : WG.M (Except Int Route) := do
  let some r := route | invariant "send6 without a route"
  return .ok r

def routeFront (cache : Option PeerId) (gen : Nat) (fallback : Option Route)
    (rt : Except Int Route) : WG.M (Except Int Route) := do
  let mut route := fallback
  match rt with
  | .error err =>
    if ← branch .send6RouteErr true then return .error err
  | .ok r =>
    _ ← branch .send6RouteErr false
    if ← branch .send6CacheSet cache.isSome then dstCacheSet cache.get! r.src gen r.dev
    route := some r
  finishFront route

def missFront (e : Endpoint) (cache : Option PeerId) (gen : Nat) (fallback : Option Route)
    (saddr : Nat) : WG.M (Except Int Route) := do
  let mut saddr := saddr
  let w ← getRouting
  let notLocal := saddr != 0 && !(saddr == 1 || saddr == LO_LINK_LOCAL || w.addrs6.contains saddr)
  if ← branch .send6SrcNotLocal notLocal then
    clear cache
    saddr := 0
    if ← branch .send6Reset cache.isSome then dstCacheReset cache.get!
  let rt ← Net.routeLookup 6 saddr e.addr
  routeFront cache gen fallback rt

def afterCacheFront (e : Endpoint) (cache : Option PeerId) (gen saddr : Nat)
    (route : Option Route) : WG.M (Except Int Route) := do
  if ← branch .send6CacheMiss route.isNone then missFront e cache gen route saddr
  else finishFront route

def front (e : Endpoint) (cache : Option PeerId) : WG.M (Except Int Route) := do
  let d ← getDev
  if ← branch .send6SockNull d.sock6.isNone then return .error (-ENONET)
  let gen := (← getRouting).ipv6Gen
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← branch .send6HasCache cache.isSome then
    let some pid := cache | invariant "unreachable"
    if let some s ← dstCacheGet pid gen then
      route := some {dev := s.dev,src := s.src}; saddr := s.src
  afterCacheFront e cache gen saddr route

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem invariant_bind (s : String) (f : α → WG.M β) :
    ((invariant s : WG.M α) >>= f) = invariant s := rfl


open Lean Meta Elab Tactic in
elab "cached6_intro" : tactic => do
  let (fid,goal) ← (← getMainGoal).intro1
  replaceMainGoal [goal]
  withMainContext do
    let ty ← withReducible (whnf (← inferType (.fvar fid)))
    if ty.isAppOf ``Bool || ty.isAppOf ``Option || ty.isAppOf ``Except then
      let branches ← goal.cases fid
      replaceMainGoal (branches.toList.map (·.mvarId))

theorem source_eq (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    source e cache bytes ds exactRx = send6 e cache bytes ds exactRx := by
  cases cache <;> unfold source send6 afterCache miss routeDone finish clear
  all_goals repeat' first
    | with_reducible rfl
    | simp +failIfUnchanged only [Bool.false_eq_true,↓reduceIte,Option.isSome_some,Option.isSome_none,Option.isNone_none,Option.isNone_some]
    | simp +failIfUnchanged only [bind_assoc,pure_bind,invariant_bind]
    | with_reducible apply source_bind
    | cached6_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem front_eq (e : Endpoint) (cache : Option PeerId) : front e cache = socket6Front e cache := by
  cases cache <;> unfold front socket6Front afterCacheFront missFront routeFront finishFront clear
  all_goals repeat' first
    | with_reducible rfl
    | simp +failIfUnchanged only [Bool.false_eq_true,↓reduceIte,Option.isSome_some,Option.isSome_none,Option.isNone_none,Option.isNone_some]
    | simp +failIfUnchanged only [bind_assoc,pure_bind,invariant_bind]
    | with_reducible apply source_bind
    | cached6_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split


theorem finish_factor (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) (route : Option Route) :
    finish e bytes ds exactRx route = (finishFront route >>= socketResult e bytes ds exactRx) := by
  cases route <;> simp [finish,finishFront,socketResult,invariant_bind,tunnelXmitSource_eq]

theorem route_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (gen : Nat) (fallback : Option Route) (rt : Except Int Route) :
    routeDone e cache bytes ds exactRx gen fallback rt =
      (routeFront cache gen fallback rt >>= socketResult e bytes ds exactRx) := by
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
      (missFront e cache gen fallback saddr >>= socketResult e bytes ds exactRx) := by
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
      (afterCacheFront e cache gen saddr route >>= socketResult e bytes ds exactRx) := by
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
    (exactRx : Bool) : source e cache bytes ds exactRx = (front e cache >>= socketResult e bytes ds exactRx) := by
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
theorem factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    send6 e cache bytes ds exactRx = (do
      match ← socket6Front e cache with
      | .error err => pure err
      | .ok r => tunnelXmitSource e bytes ds r exactRx; pure 0) := by
  rw [← source_eq,source_factor,front_eq]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.Socket6Cached
