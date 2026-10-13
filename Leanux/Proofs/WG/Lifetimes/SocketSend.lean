import Leanux.Proofs.WG.Lifetimes.SocketCache
import Leanux.Proofs.WG.Lifetimes.AllocationAmbient

/-! Complete tunnel and IPv6 socket send paths. IPv4 send remains a separate
caller obligation. Routing and record effects are lifted only
where source inspection shows no peer/keypair/packet access. -/
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

structure SocketContracts (I : List LifetimeEvent → World → Prop) : Prop where
  stats : ∀ P count, AmbientSpec I P
    (liftPrefix (modifyDev fun d => {d with txPackets := d.txPackets + 1, txBytes := d.txBytes + count}))
    (fun _ => P)

theorem allocationSocket : SocketContracts AllocationInv where
  stats := by
    intro P count
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.safe)
    intro h w x v hi hr
    have hf : (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
      cases hr
      unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata
      simp [Option.bind_map, Function.comp_def, deviceAllocationMetadata]
      rfl
    have he : identityView v = identityView w := congrArg Prod.fst hf
    exact ⟨hi.1.congr he (congrArg Prod.snd hf), he ▸ hi.2⟩

def tunnelXmitSource (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) : M Unit := do
  if r.dev == WG0_IFINDEX then unsupported "a datagram routed back into wg0"
  if exactRx then loopbackSend ([.ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts) true
  else skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx]

  modifyDev fun d => { d with txPackets := d.txPackets + 1, txBytes := d.txBytes + bytes.length }
  let sport ← socketPort e.family
  modify fun w => { w with sent := w.sent ++ [{ family := e.family, addr := e.addr, port := e.port, bytes, ds, sport, src := r.src }] }

def tunnelXmitPrefix (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) : MixedM Unit := do
  if r.dev == WG0_IFINDEX then liftPrefix (unsupported "a datagram routed back into wg0")
  if exactRx then loopbackSendPrefix ([.ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts) true
  else liftPrefix (skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx])
  liftPrefix (modifyDev fun d => { d with txPackets := d.txPackets + 1, txBytes := d.txBytes + bytes.length })
  let sport ← liftPrefix (socketPort e.family)
  liftPrefix (modify fun w => { w with sent := w.sent ++ [{ family := e.family, addr := e.addr, port := e.port, bytes, ds, sport, src := r.src }] })

theorem tunnelXmitSource_eq (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx =
      tunnelXmitSource e bytes ds r exactRx := rfl

theorem tunnelXmitPrefix_erases (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    ErasesPrefix (tunnelXmitPrefix e bytes ds r exactRx)
      ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  unfold tunnelXmitPrefix tunnelXmitSource
  repeat' first
    | exact loopbackSendPrefix_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | split
    | (intro x; try dsimp only)

theorem tunnelXmitPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    AmbientSpec I P (tunnelXmitPrefix e bytes ds r exactRx) (fun _ => P) := by
  unfold tunnelXmitPrefix
  repeat' first
    | exact c.unsupported P _
    | exact loopbackSendPrefix_spec c P _ _
    | exact c.kernel P _ (skipCut_sameKernel _)
    | exact sc.stats P _
    | exact c.kernel P _ (socketPort_sameKernel _)
    | exact c.kernel P _ (by intro w x v hr; cases hr; rfl)
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

def send6Prefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) : MixedM Int := do
  let d ← liftPrefix getDev
  if ← liftPrefix (branch .send6SockNull d.sock6.isNone) then return -ENONET
  let gen := (← liftPrefix (get : M World)).ipv6Gen
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← liftPrefix (branch .send6HasCache cache.isSome) then
    let some pid := cache | liftPrefix (invariant "unreachable")
    if let some s ← dstCacheGetPrefix pid gen then
      route := some { dev := s.dev, src := s.src }; saddr := s.src
  if ← liftPrefix (branch .send6CacheMiss route.isNone) then

    let w ← liftPrefix (get : M World)
    let notLocal := saddr != 0 && !(saddr == 1 || saddr == LO_LINK_LOCAL || w.addrs6.contains saddr)
    if ← liftPrefix (branch .send6SrcNotLocal notLocal) then
      if let some pid := cache then
        modifyPeerKeysPrefix pid fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0}}
      saddr := 0
      if ← liftPrefix (branch .send6Reset cache.isSome) then dstCacheResetMixed cache.get!
    match ← liftPrefix (routeLookup 6 saddr e.addr) with
    | .error err =>
      if ← liftPrefix (branch .send6RouteErr true) then return err
    | .ok r =>
      _ ← liftPrefix (branch .send6RouteErr false)
      if ← liftPrefix (branch .send6CacheSet cache.isSome) then dstCacheSetPrefix cache.get! r.src gen r.dev
      route := some r
  let some r := route | liftPrefix (invariant "send6 without a route")
  tunnelXmitPrefix e bytes ds r exactRx
  return 0

/-- Compose an immediate peer read/update with an independent continuation.
This only reassociates the already-proved original helper contract. -/
theorem socketUpdate_bind_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (f : Peer → Peer) (hf : ∀ p, (f p).internalId = p.internalId)
    (g : MixedM α) (Q : α → IdentityView → Prop) (hg : AmbientSpec I P g Q) :
    AmbientSpec I P (do let p ← getPeerMixed pid; setPeerMixed pid (f p); g) Q := by
  simpa only [modifyPeerKeysPrefix, bind_assoc] using
    PrefixEnsures.bind (modifyPeerKeysPrefix_spec_ambient c P pid f hf) (fun _ => hg)

theorem send6Prefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ErasesPrefix (send6Prefix e cache bytes ds exactRx) (send6 e cache bytes ds exactRx) := by
  cases cache <;> unfold send6Prefix send6
  all_goals simp only [modifyPeerKeysPrefix, map_eq_pure_bind, bind_assoc]
  all_goals repeat' first
    | contradiction
    | with_reducible assumption
    | with_reducible exact dstCacheGetPrefix_erases _ _
    | with_reducible exact dstCacheResetMixed_erases _
    | with_reducible exact dstCacheSetPrefix_erases _ _ _ _
    | with_reducible exact tunnelXmitPrefix_erases _ _ _ _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | (intro_forall <;> try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false])
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false])
    | rfl
  all_goals simp_all

theorem send6Prefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    AmbientSpec I P (send6Prefix e cache bytes ds exactRx) (fun _ => P) := by
  have getWorld : AmbientSpec I P (liftPrefix (get : M World)) (fun _ => P) :=
    c.kernel P _ (by intro w x v hr; cases hr; rfl)
  have update (pid : PeerId) :
      AmbientSpec I P (modifyPeerKeysPrefix pid
        (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0}}))
        (fun _ => P) :=
    modifyPeerKeysPrefix_spec_ambient c P pid
      (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0}}) (fun _ => rfl)
  cases cache <;> unfold send6Prefix
  all_goals simp only [map_eq_pure_bind, bind_assoc]
  all_goals repeat' first
    | contradiction
    | with_reducible assumption
    | with_reducible exact dstCacheGetPrefix_spec c P _ _
    | with_reducible exact dstCacheResetMixed_spec c P _
    | with_reducible exact dstCacheSetPrefix_spec c P _ _ _ _
    | with_reducible exact tunnelXmitPrefix_spec c sc P _ _ _ _ _
    | with_reducible exact update _
    | with_reducible apply socketUpdate_bind_spec c P _ _ (fun _ => rfl)
    | with_reducible exact c.kernel P _ getDev_sameKernel
    | with_reducible exact c.kernel P _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact getWorld
    | with_reducible exact c.branch P _ _
    | with_reducible exact c.invariant P _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.ite
    | with_reducible apply PrefixEnsures.bind
    | (intro_forall <;> try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false])
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false])

end Leanux.Proofs.WG.Lifetimes
