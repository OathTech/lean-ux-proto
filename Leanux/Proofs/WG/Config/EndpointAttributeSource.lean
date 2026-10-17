import Leanux.Proofs.WG.Config.EndpointSetSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- The actual attribute branch, including both decision records. -/
def endpointAttributeUpdate (pid : PeerId) (a : EndpointAttr) : WG.M Unit := do
  if ← WG.andM (branch .peerEndpointV4Len (a.len == 16)) (branch .peerEndpointV4Family (a.family == AF_INET)) then
    setPeerEndpoint pid {family := a.family, addr := a.addr, port := a.port}
  else if ← WG.andM (branch .peerEndpointV6Len (a.len == 28)) (branch .peerEndpointV6Family (a.family == AF_INET6)) then
    setPeerEndpoint pid {family := a.family, addr := a.addr, port := a.port, scope := a.scope, flowinfo := a.flowinfo}

private theorem endpoint_branch {α : Type} (site : Decision) (value : Bool)
    (a : WG.M α) (P : WGWorld → Prop) (Q : α → WGWorld → Prop) (body : Ensures a P Q) :
    Ensures (do _ ← branch site value; a) P Q := by
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (branch_state_spec P site value)) ?_
  intro ret g ambient result final after pre run
  exact body g ambient result final after pre.2 run

theorem endpointAttribute_exact (pid : PeerId) (a : EndpointAttr) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (endpointAttributeUpdate pid a)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => ∃ reset, g.dev = some (endpointAttributeStores d pid p a reset) ∧
        readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => g.dev = some d ∧ readbackFrame g sock fixtures
  have comparison (l f : Decision) (x y : Bool) :
      Ensures (WG.andM (branch l x) (branch f y)) P (fun value g => value = (x && y) ∧ P g) := by
    intro g ambient value final after pre run
    obtain ⟨actual, middle, next, closed, facts⟩ := endpointAnd_returns _ _ x y P
      ((returns_iff _ _ _).mpr (branch_state_returns P l x))
      ((returns_iff _ _ _).mpr (branch_state_returns P f y)) g ambient pre
    rw [closed] at run
    cases run
    exact facts
  unfold endpointAttributeUpdate
  refine ensures_bind _ _ (comparison .peerEndpointV4Len .peerEndpointV4Family (a.len == 16) (a.family == AF_INET)) ?_
  intro value g ambient result final after pre run
  obtain ⟨hv, hp⟩ := pre
  subst value
  cases v4 : a.len == 16 && a.family == AF_INET with
  | true =>
    simp only [v4, ↓reduceIte] at run
    have family : a.family = AF_INET := (by simpa using v4 : a.len = 16 ∧ a.family = AF_INET).2
    obtain ⟨reset, effect, frame, _⟩ := setPeerEndpoint_exact pid
      {family := a.family, addr := a.addr, port := a.port} d p resident (Or.inl family)
      sock fixtures g ambient result final after hp run
    exact ⟨reset, by simpa [endpointAttributeStores, endpointAttribute, v4] using effect, frame⟩
  | false =>
    simp only [v4, Bool.false_eq_true, ↓reduceIte] at run
    have second : Ensures (do
        if ← WG.andM (branch .peerEndpointV6Len (a.len == 28)) (branch .peerEndpointV6Family (a.family == AF_INET6)) then
          setPeerEndpoint pid {family := a.family, addr := a.addr, port := a.port, scope := a.scope, flowinfo := a.flowinfo}) P
        (fun _ g => ∃ reset, g.dev = some (endpointAttributeStores d pid p a reset) ∧ readbackFrame g sock fixtures) := by
      refine ensures_bind _ _ (comparison .peerEndpointV6Len .peerEndpointV6Family (a.len == 28) (a.family == AF_INET6)) ?_
      intro value g ambient result final after pre run
      obtain ⟨hv, hp⟩ := pre
      subst value
      cases v6 : a.len == 28 && a.family == AF_INET6 with
      | true =>
        simp only [v6, ↓reduceIte] at run
        have family : a.family = AF_INET6 := (by simpa using v6 : a.len = 28 ∧ a.family = AF_INET6).2
        obtain ⟨reset, effect, frame, _⟩ := setPeerEndpoint_exact pid
          {family := a.family, addr := a.addr, port := a.port, scope := a.scope, flowinfo := a.flowinfo}
          d p resident (Or.inr family) sock fixtures g ambient result final after hp run
        exact ⟨reset, by simpa [endpointAttributeStores, endpointAttribute, v4, v6] using effect, frame⟩
      | false =>
        simp only [v6, Bool.false_eq_true, ↓reduceIte] at run
        cases run
        exact ⟨none, by simpa [endpointAttributeStores, endpointAttribute, v4, v6] using hp.1, hp.2⟩
    exact second g ambient result final after hp run

/-- Store effects expose the resident configured peer without assuming map
idempotence. No field other than endpoint/cache is changed by this branch. -/
theorem endpointAttributeStores_fields (d : Device) (pid : PeerId) (p : Peer) (a : EndpointAttr)
    (reset : Option UInt64) (resident : d.peers[pid]? = some p) :
    (endpointAttributeStores d pid p a reset).peers[pid]? = some (endpointAttributePeer p a reset) ∧
    withoutPeers (endpointAttributeStores d pid p a reset) = withoutPeers d ∧
    (endpointAttributePeer p a reset).refcount = p.refcount ∧
    (endpointAttributePeer p a reset).allowedipsList = p.allowedipsList ∧
    peerFixedAttrs (endpointAttributePeer p a reset) = peerFixedAttrs (endpointApplied p a) ∧
    peerFixedSpace (endpointAttributePeer p a reset) = peerFixedSpace (endpointApplied p a) := by
  cases decoded : endpointAttribute a with
  | none => simp [endpointAttributeStores, endpointAttributePeer, endpointApplied, decoded, resident]
  | some e =>
    cases equal : endpointSame e p.endpoint <;> cases reset <;>
      simp [endpointAttributeStores, endpointAttributePeer, endpointApplied, decoded,
        endpointStores, endpointStoredPeer, equal, withPeer, withoutPeers, resident,
        peerFixedAttrs, peerFixedSpace]

theorem endpointTail_down (key : Key) (a : EndpointAttr) (updateOnly : Bool) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (down : d.running = false) (retained : 1 < p.refcount)
    (sock : NlSock) (fixtures : FixtureDevices) :
    Returns (peerConfigTailSource (endpointPeerAttrs key a updateOnly) (some pid) pid)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun ret g => ret = 0 ∧ g.dev = some (withPeer d pid {p with refcount := p.refcount - 1}) ∧ readbackFrame g sock fixtures) := by
  intro g ambient pre
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .peerHasAips false) .peerHasKeepalive false) .peerRunning false
  obtain ⟨value, out, after, run, effect, frame⟩ :=
    (returns_iff _ _ _).mpr (peerPut_retained_returns_framed sock fixtures pid d p resident retained) g before pre
  cases value
  refine ⟨0, out, mark after .peerZeroPsk false, ?_, rfl, effect, frame⟩
  simp [peerConfigTailSource, endpointPeerAttrs, getDev, pre.1, down, branch, AmbientM.branch]
  rw [show ((peerPut (some pid)).run g).run before = .ok (((), out), after) from run]
  rfl

/-- Existing peers take the same update path with or without UPDATE_ONLY. -/
theorem endpointUpdate_down (key : Key) (a : EndpointAttr) (updateOnly : Bool) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (down : d.running = false) (retained : 1 < p.refcount)
    (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (peerConfigUpdateSource (endpointPeerAttrs key a updateOnly) (some pid)
        (if updateOnly then WGPEER_F_UPDATE_ONLY else 0) none pid)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun ret g => ret = 0 ∧ ∃ reset,
        g.dev = some (withPeer (endpointAttributeStores d pid p a reset) pid
          {(endpointAttributePeer p a reset) with refcount := (endpointAttributePeer p a reset).refcount - 1}) ∧
        readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => g.dev = some d ∧ readbackFrame g sock fixtures
  let Q : Int → WGWorld → Prop := fun ret g => ret = 0 ∧ ∃ reset,
    g.dev = some (withPeer (endpointAttributeStores d pid p a reset) pid
      {(endpointAttributePeer p a reset) with refcount := (endpointAttributePeer p a reset).refcount - 1}) ∧
    readbackFrame g sock fixtures
  have core : Ensures (do
      endpointAttributeUpdate pid a
      _ ← branch .peerReplaceAips false
      peerConfigTailSource (endpointPeerAttrs key a updateOnly) (some pid) pid) P Q := by
    refine ensures_bind _ _ (endpointAttribute_exact pid a d p resident sock fixtures) ?_
    intro ignored g ambient ret final after pre run
    obtain ⟨reset, device, frame⟩ := pre
    have fields := endpointAttributeStores_fields d pid p a reset resident
    have running : (endpointAttributeStores d pid p a reset).running = false := by
      have same := congrArg Device.running fields.2.1
      exact same.trans down
    have tail : Ensures (peerConfigTailSource (endpointPeerAttrs key a updateOnly) (some pid) pid)
        (fun g => g.dev = some (endpointAttributeStores d pid p a reset) ∧ readbackFrame g sock fixtures) Q := by
      intro entry before value out rest initial executed
      obtain ⟨actual, current, remaining, closed, code, effect, framed⟩ :=
        endpointTail_down key a updateOnly pid (endpointAttributeStores d pid p a reset)
          (endpointAttributePeer p a reset) fields.1 running
          (by simpa only [fields.2.2.1] using retained) sock fixtures entry before initial
      rw [closed] at executed
      cases executed
      exact ⟨code, reset, effect, framed⟩
    exact endpoint_branch .peerReplaceAips false _ _ _ tail g ambient ret final after ⟨device, frame⟩ run
  have decorated := endpoint_branch .peerRemoveMe false _ P Q
    (endpoint_branch .peerSetPsk false _ P Q (endpoint_branch .peerHasEndpoint true _ P Q core))
  have source : peerConfigUpdateSource (endpointPeerAttrs key a updateOnly) (some pid)
      (if updateOnly then WGPEER_F_UPDATE_ONLY else 0) none pid = (do
        _ ← branch .peerRemoveMe false
        _ ← branch .peerSetPsk false
        _ ← branch .peerHasEndpoint true
        endpointAttributeUpdate pid a
        _ ← branch .peerReplaceAips false
        peerConfigTailSource (endpointPeerAttrs key a updateOnly) (some pid) pid) := by
    let mark (site : Decision) (value : Bool) : WG.M Unit :=
      monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
        decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
    have branchSource (site : Decision) (value : Bool) :
        (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
    have ifBind {α β : Type} (condition : Prop) [Decidable condition]
        (yes no : WG.M α) (finish : α → WG.M β) :
        ((if condition then yes else no) >>= finish) =
          (if condition then yes >>= finish else no >>= finish) := by split <;> rfl
    cases updateOnly <;> simp [peerConfigUpdateSource, endpointPeerAttrs, endpointAttributeUpdate,
      WGPEER_F_REMOVE_ME, WGPEER_F_REPLACE_ALLOWEDIPS, WGPEER_F_UPDATE_ONLY, WG.andM,
      branchSource, bind_assoc, ifBind]
    all_goals rfl
  rw [source]
  exact decorated

/-- Full original set_peer, including the real lookup acquire and out release. -/
theorem setPeer_endpoint_down (key : Key) (a : EndpointAttr) (updateOnly : Bool) (pid : PeerId)
    (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (setPeerCmd (endpointPeerAttrs key a updateOnly))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun ret g => ret = 0 ∧ ∃ reset,
        g.dev = some (endpointSetterDevice d pid p a reset) ∧ readbackFrame g sock fixtures) := by
  intro g ambient ret final after pre run
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark (mark (mark ambient .peerHasPubkey true)
    .peerPubkeyLen true) .peerHasPsk false) .peerHasFlags updateOnly) .peerBadFlags false) .peerHasProtocol false
  obtain ⟨value, middle, next, lookupRun, code, device, frame⟩ :=
    (returns_iff _ _ _).mpr (pubkeyLookup_present_returns_framed sock fixtures key pid d p
      found resident live bounded) g before pre
  subst value
  let acquired := {p with refcount := p.refcount + 1}
  let changed := withPeer d pid acquired
  let start := mark next .peerNotFound false
  have actual : ((peerConfigUpdateSource (endpointPeerAttrs key a updateOnly) (some pid)
      (if updateOnly then WGPEER_F_UPDATE_ONLY else 0) none pid).run middle).run start =
        .ok ((ret, final), after) := by
    rw [← setPeerCmd_source] at run
    have updateValid : (4 : UInt32) &&& ~~~7 = 0 := rfl
    cases updateOnly
    all_goals simp [setPeerCmdSource, endpointPeerAttrs, WG.andM, branch, AmbientM.branch,
      WGPEER_F_ALL, WGPEER_F_UPDATE_ONLY, updateValid, before, mark, lookupRun] at run
    all_goals dsimp only [Bind.bind, Except.bind] at run
    all_goals exact run
  have result := endpointUpdate_down key a updateOnly pid changed acquired
    (by simp [changed, withPeer]) down (by dsimp [acquired]; omega) sock fixtures
    middle start ret final after ⟨device, frame⟩ actual
  exact result

end Leanux.Proofs.WG.Config
