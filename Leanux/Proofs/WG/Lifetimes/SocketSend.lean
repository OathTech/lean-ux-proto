import Leanux.Proofs.WG.Lifetimes.SocketCache
import Leanux.Proofs.WG.Lifetimes.AllocationAmbient

/-! Complete tunnel and IPv6 socket send paths. The IPv4 observer is
in SocketSend4. Routing and record effects are lifted only
where source inspection shows no peer/keypair/packet access. -/
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

structure SocketContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  stats : ∀ P count, AmbientSpec I P
    (liftWGPrefix (modifyDev fun d => {d with txPackets := d.txPackets + 1, txBytes := d.txBytes + count}))
    (fun _ => P)

structure ProductSocketContracts (I : List LifetimeEvent → World → Prop) : Prop where
  stats : ∀ P count, ProductAmbientSpec I P
    (liftWGObserver (liftWGPrefix (modifyDev fun d =>
      {d with txPackets := d.txPackets + 1, txBytes := d.txBytes + count})))
    (fun _ => P)

theorem allocationSocket : SocketContracts AllocationInv where
  stats := by
    intro P count
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.safe)
    intro h w ambient x v ambient' hi hr
    have hf : (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
      cases hr
      unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata
      simp [Option.bind_map, Function.comp_def, deviceAllocationMetadata]
      rfl
    have he : identityView v = identityView w := congrArg Prod.fst hf
    exact ⟨hi.1.congr he (congrArg Prod.snd hf), he ▸ hi.2⟩

def tunnelXmitSource (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) : WG.M Unit := do
  if r.dev == WG0_IFINDEX then unsupported "a datagram routed back into wg0"
  if exactRx then loopbackSend ([.ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts) true
  else skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx]

  modifyDev fun d => { d with txPackets := d.txPackets + 1, txBytes := d.txBytes + bytes.length }
  let sport ← socketPort e.family
  modify fun w => { w with sent := w.sent ++ [{ family := e.family, addr := e.addr, port := e.port, bytes, ds, sport, src := r.src }] }

def tunnelXmitPrefix (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) : MixedM Unit := do
  if r.dev == WG0_IFINDEX then liftWGPrefix (unsupported "a datagram routed back into wg0")
  if exactRx then loopbackSendPrefix ([.ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts) true
  else liftWGPrefix (skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx])
  liftWGPrefix (modifyDev fun d => { d with txPackets := d.txPackets + 1, txBytes := d.txBytes + bytes.length })
  let sport ← liftWGPrefix (socketPort e.family)
  liftWGPrefix (modify fun w => { w with sent := w.sent ++ [{ family := e.family, addr := e.addr, port := e.port, bytes, ds, sport, src := r.src }] })

theorem tunnelXmitSource_eq (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx =
      tunnelXmitSource e bytes ds r exactRx := rfl

theorem tunnelXmitPrefix_erases (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    ErasesStatePrefix (tunnelXmitPrefix e bytes ds r exactRx)
      ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  unfold tunnelXmitPrefix tunnelXmitSource
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head loopbackSendPrefix; exact loopbackSendPrefix_erases _ _)
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | maintenance_erases_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem tunnelXmitPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    AmbientSpec I P (tunnelXmitPrefix e bytes ds r exactRx) (fun _ => P) := by
  unfold tunnelXmitPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_lift_action_head unsupported; exact c.store P _
        (fun initial => hoare_liftAmbient (AmbientM.unsupported _) _))
    | (maintenance_head loopbackSendPrefix; exact loopbackSendPrefix_spec c P _ _)
    | (maintenance_lift_action_head skipCut; exact c.store P _
        (fun initial => hoare_liftAmbient (AmbientM.skipCut _) _))
    | (maintenance_lift_action_head modifyDev; exact sc.stats P _)
    | (maintenance_lift_action_head socketPort; exact c.store P _ (socketPort_sameStore _))
    | (maintenance_lift_action_head modify; exact c.store P _
        (by intro initial; apply hoare_modify; intro w hw; exact hw))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

def send6Prefix (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) : MixedM Int := do
  let d ← liftWGPrefix getDev
  if ← liftWGPrefix (branch .send6SockNull d.sock6.isNone) then return -ENONET
  let gen := (← liftWGPrefix (getRouting : WG.M Net.Routing)).ipv6Gen
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← liftWGPrefix (branch .send6HasCache cache.isSome) then
    let some pid := cache | liftWGPrefix (invariant "unreachable")
    if let some s ← dstCacheGetPrefix pid gen then
      route := some { dev := s.dev, src := s.src }; saddr := s.src
  if ← liftWGPrefix (branch .send6CacheMiss route.isNone) then

    let w ← liftWGPrefix (getRouting : WG.M Net.Routing)
    let notLocal := saddr != 0 && !(saddr == 1 || saddr == LO_LINK_LOCAL || w.addrs6.contains saddr)
    if ← liftWGPrefix (branch .send6SrcNotLocal notLocal) then
      if let some pid := cache then
        modifyPeerKeysPrefix pid fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0}}
      saddr := 0
      if ← liftWGPrefix (branch .send6Reset cache.isSome) then dstCacheResetMixed cache.get!
    match ← liftWGPrefix (liftRouting (Net.routeLookup 6 saddr e.addr)) with
    | .error err =>
      if ← liftWGPrefix (branch .send6RouteErr true) then return err
    | .ok r =>
      _ ← liftWGPrefix (branch .send6RouteErr false)
      if ← liftWGPrefix (branch .send6CacheSet cache.isSome) then dstCacheSetPrefix cache.get! r.src gen r.dev
      route := some r
  let some r := route | liftWGPrefix (invariant "send6 without a route")
  tunnelXmitPrefix e bytes ds r exactRx
  return 0

/-- Compose an immediate peer read/update with an independent continuation.
This only reassociates the already-proved original helper contract. -/
theorem socketUpdate_bind_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (f : Peer → Peer) (hf : ∀ p, (f p).internalId = p.internalId)
    (g : MixedM α) (Q : α → IdentityView → Prop) (hg : AmbientSpec I P g Q) :
    AmbientSpec I P (do let p ← getPeerMixed pid; setPeerMixed pid (f p); g) Q := by
  simpa only [modifyPeerKeysPrefix, bind_assoc] using
    StatePrefixEnsures.bind (modifyPeerKeysPrefix_spec_ambient c P pid f hf) (fun _ => hg)

theorem send6Prefix_erases (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ErasesStatePrefix (send6Prefix e cache bytes ds exactRx) (send6 e cache bytes ds exactRx) := by
  unfold send6Prefix send6 modifyPeerKeysPrefix
  simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_erases _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_erases _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_erases _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_erases _ _ _ _ _)
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | maintenance_erases_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem send6Prefix_spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    AmbientSpec I P (send6Prefix e cache bytes ds exactRx) (fun _ => P) := by
  have getRoutingSpec : AmbientSpec I P (liftWGPrefix (getRouting : WG.M Net.Routing)) (fun _ => P) :=
    c.store P _ (fun initial => by
      unfold getRouting
      exact hoare_liftRouting
        ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
        (fun w => wgStoreView w = initial) (fun _ _ hi => hi))
  have update (pid : PeerId) :
      AmbientSpec I P (modifyPeerKeysPrefix pid
        (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0}}))
        (fun _ => P) :=
    modifyPeerKeysPrefix_spec_ambient c P pid
      (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0}}) (fun _ => rfl)
  unfold send6Prefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec c P _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec c P _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec c P _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec c sc P _ _ _ _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact update _)
    | (maintenance_lift_action_head getDev; exact c.store P _
        (by intro initial; unfold Hoare; mvcgen [getDev, invariant, AmbientM.invariant]))
    | (maintenance_lift_action_head liftRouting; exact c.store P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact getRoutingSpec)
    | (maintenance_lift_action_head branch; exact c.store P _
        (fun initial => hoare_liftAmbient (AmbientM.branch _ _) _))
    | (maintenance_lift_action_head invariant; exact c.store P _
        (fun initial => hoare_liftAmbient (AmbientM.invariant _) _))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem tunnelXmitPrefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    ProductAmbientSpec I P (liftWGObserver (tunnelXmitPrefix e bytes ds r exactRx)) (fun _ => P) := by
  unfold tunnelXmitPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_lift_action_head unsupported; exact c.nativeStore P _
        (fun initial => hoare_liftAmbient (AmbientM.unsupported _) _))
    | (maintenance_head loopbackSendPrefix; exact loopbackSendPrefix_spec_product c P _ _)
    | (maintenance_lift_action_head skipCut; exact c.nativeStore P _
        (fun initial => hoare_liftAmbient (AmbientM.skipCut _) _))
    | (maintenance_lift_action_head modifyDev; exact sc.stats P _)
    | (maintenance_lift_action_head socketPort; exact c.nativeStore P _ (socketPort_sameStore _))
    | (maintenance_lift_action_head modify; exact c.nativeStore P _
        (by intro initial; apply hoare_modify; intro w hw; exact hw))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind)
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem socketUpdate_bind_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (f : Peer → Peer) (hf : ∀ p, (f p).internalId = p.internalId)
    (g : PrefixM LifetimeEvent α) (Q : α → IdentityView → Prop)
    (hg : ProductAmbientSpec I P g Q) :
    ProductAmbientSpec I P (do
      let p ← liftWGObserver (getPeerMixed pid)
      liftWGObserver (setPeerMixed pid (f p))
      g) Q := by
  simpa only [modifyPeerKeysPrefix, liftWGObserver_bind, bind_assoc] using
    PrefixEnsures.bind (modifyPeerKeysPrefix_spec_product c P pid f hf) (fun _ => hg)

theorem send6Prefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I) (P : IdentityView → Prop)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ProductAmbientSpec I P (liftWGObserver (send6Prefix e cache bytes ds exactRx)) (fun _ => P) := by
  have getRoutingSpec : ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (getRouting : WG.M Net.Routing))) (fun _ => P) :=
    c.nativeStore P _ (fun initial => by
      unfold getRouting
      exact hoare_liftRouting
        ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
        (fun w => wgStoreView w = initial) (fun _ _ hi => hi))
  have update (pid : PeerId) :
      ProductAmbientSpec I P (liftWGObserver (modifyPeerKeysPrefix pid
        (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0}})))
        (fun _ => P) :=
    modifyPeerKeysPrefix_spec_product c P pid
      (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0}}) (fun _ => rfl)
  unfold send6Prefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head dstCacheGetPrefix; exact dstCacheGetPrefix_spec_product c P _ _)
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec_product c P _)
    | (maintenance_head dstCacheSetPrefix; exact dstCacheSetPrefix_spec_product c P _ _ _ _)
    | (maintenance_head tunnelXmitPrefix; exact tunnelXmitPrefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact update _)
    | (maintenance_lift_action_head getDev; exact c.nativeStore P _
        (by intro initial; unfold Hoare; mvcgen [getDev, invariant, AmbientM.invariant]))
    | (maintenance_lift_action_head liftRouting; exact c.nativeStore P _
        (fun initial => hoare_liftRouting _ _ (fun _ _ hi => hi)))
    | (maintenance_lift_action_head getRouting; exact getRoutingSpec)
    | (maintenance_lift_action_head branch; exact c.nativeStore P _
        (fun initial => hoare_liftAmbient (AmbientM.branch _ _) _))
    | (maintenance_lift_action_head invariant; exact c.nativeStore P _
        (fun initial => hoare_liftAmbient (AmbientM.invariant _) _))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind)
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

end Leanux.Proofs.WG.Lifetimes
