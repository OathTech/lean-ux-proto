import Leanux.Proofs.WG.Config.SocketReadbackScanSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def socketDumpHeaderSource {m : Type → Type} [Monad m] [MonadLiftT AmbientM m] (d : Device) (ctx0 : DumpCtx) (prevSeq0 : Nat) (skb0 : NlSkb)
    (finish : Nat → List (String × Json) → NlSkb → m DumpCall) : m DumpCall := do
  let seq := d.deviceUpdateGen   -- cb->seq (:222)
  let mut ctx := ctx0
  let (fail, skb) := skb0.put (nlmsgTotal 4)   -- genlmsg_put: nlmsghdr + genlmsghdr
  if ← branch .dumpNoHdr fail then unsupported "a dump chunk without room for its header (unreachable: every chunk is fresh)"
  let mut skb := skb
  -- genl_dump_check_consistent (:229): NLM_F_DUMP_INTR iff the device changed
  -- between two dump calls (2.4); NLM_F_MULTI always
  let flags := 2 + (if prevSeq0 != 0 && prevSeq0 != seq then 16 else 0)
  let mut device : List (String × Json) := []
  if ← branch .dumpFirst ctx.nextPeer.isNone then
    let (fail, s) := skb.put (nlaTotal 2); skb := s
    if ← branch .dumpPutPort fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
    let (fail, s) := skb.put (nlaTotal 4); skb := s
    if ← branch .dumpPutFwmark fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
    let (fail, s) := skb.put (nlaTotal 4); skb := s
    if ← branch .dumpPutIfindex fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
    let (fail, s) := skb.put (nlaTotal (d.ifname.length + 1)); skb := s
    if ← branch .dumpPutIfname fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
    device := [("listen_port", toJson d.incomingPort), ("fwmark", toJson d.fwmark),
      ("ifindex", toJson d.ifindex), ("ifname", toJson d.ifname)]
    let identity := d.staticIdentity
    if ← branch .dumpHasIdentity identity.hasIdentity then
      let (fail, s) := skb.put (nlaTotal 32); skb := s
      if ← branch .dumpPutPrivate fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
      let (fail, s) := skb.put (nlaTotal 32); skb := s
      if ← branch .dumpPutPublic fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
      device := device ++ [("private_key", toJson (hexKey identity.staticPrivate)),
        ("public_key", toJson (hexKey identity.staticPublic))]
  finish flags device skb

def socketDumpPeerSource (d : Device) (ctx0 : DumpCtx) (flags : Nat) (device : List (String × Json)) (skb : NlSkb) : WG.M DumpCall := do
  let seq := d.deviceUpdateGen
  let mut ctx := ctx0
  let mut nextCursor := ctx.nextPeer
  let mut skb := skb
  -- peers_nest = nla_nest_start(skb, WGDEVICE_A_PEERS)
  let (fail, s) := skb.put (nlaTotal 0); skb := s
  if ← branch .dumpNoPeersNest fail then unsupported "the peers nest does not fit a fresh chunk (unreachable)"
  let nestStart := skb
  let ret : Int := 0
  let mut done := true
  let mut peers : Option (Array PeerDumpAttrs) := some #[]
  let cursorDead : WG.M Bool := do
    let some pid := ctx.nextPeer | invariant "unreachable"
    return (← getPeer pid).isDead
  if ← WG.orM (branch .dumpPeerListEmpty d.peerList.isEmpty)
      (WG.andM (branch .dumpCursorSet ctx.nextPeer.isSome) (do branch .dumpCursorDead (← cursorDead))) then
    skb := nestStart   -- nla_nest_cancel(skb, peers_nest); goto out
    peers := none
  else
    -- list_prepare_entry / list_for_each_entry_continue: from the peer
    -- after the cursor (the last completed one), or the first
    let fromPeers : List PeerId := match ctx.nextPeer with
      | none => d.peerList
      | some pid => (d.peerList.dropWhile (· != pid)).drop 1
    let mut ps : Array PeerDumpAttrs := #[]
    for pid in fromPeers do
      _ ← branch .dumpPeerIter true
      -- the handshake worker updates tx_bytes
      requireNotPending pid "dumping the peer"
      let (s, c, r) ← getPeerDump pid ctx skb
      skb := s; ctx := c
      match r with
      | .complete peer =>
        _ ← branch .dumpGetPeerFail false
        ps := ps.push peer
        nextCursor := some pid
      | .split peer =>
        _ ← branch .dumpGetPeerFail true
        ps := ps.push peer
        done := false
        break
      | .cancelled =>
        _ ← branch .dumpGetPeerFail true
        done := false
        break
    if done then _ ← branch .dumpPeerIter false
    peers := some ps
  -- out: `!ret && !done && next_peer_cursor` takes the cursor's reference;
  -- the old cursor's is dropped
  if ← WG.andM (branch .dumpOutRetZero (ret == 0))
      (WG.andM (branch .dumpOutNotDone !done) (branch .dumpOutHasCursor nextCursor.isSome)) then
    let some pid := nextCursor | invariant "unreachable"
    peerGet pid
  peerPut ctx.nextPeer
  if ← branch .dumpRetErr (ret != 0) then unsupported "unreachable: the header and the nests fit"
  -- genlmsg_end: the data message is complete
  let message := NlMessage.data flags device (peers.map (·.toList))
  skb := { skb with messages := skb.messages ++ [message] }
  if ← branch .dumpDone done then
    return { ret := 0, skb, ctx := { ctx with nextPeer := none }, prevSeq := seq }
  -- `return skb->len` (:296): the chunk's bytes so far, positive once the
  -- data message is in; `netlink_dump` reads its sign (audit F2)
  return { ret := Int.ofNat (NLMSG_GOODSIZE - skb.room), skb, ctx := { ctx with nextPeer := nextCursor }, prevSeq := seq }

theorem socketDump_source (d : Device) (ctx : DumpCtx) (prev : Nat) (skb : NlSkb) :
    deviceDumpSource d ctx prev skb =
      socketDumpHeaderSource d ctx prev skb (socketDumpPeerSource d ctx) := rfl

/-- Header cut: all original put guards succeed at the stated capacity. -/
theorem socketDumpHeader_contract (d : Device) (ctx : DumpCtx) (prev : Nat)
    (finish : Nat → List (String × Json) → NlSkb → Leanux.M DumpCall) (result : DumpCall)
    (first : ctx.nextPeer = none) (consistent : prev = 0 ∨ prev = d.deviceUpdateGen)
    (fits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (hf : ∀ flags attrs skb, ⦃fun w => ⌜w.wg.dev = some d ∧ flags = 2 ∧
        attrs = deviceFixedAttrs d ∧ skb.room = NLMSG_GOODSIZE - devicePrefixSpace d + 4 ∧ skb.messages = []⌝⦄
      finish flags attrs skb ⦃⇓ q w => ⌜q = result ∧ w.wg.dev = some d⌝⦄) :
    Product.Returns (socketDumpHeaderSource d ctx prev {} finish) (fun w => w.wg.dev = some d)
      (fun q w => q = result ∧ w.wg.dev = some d) := by
  have flags : (2 + if prev ≠ 0 ∧ prev ≠ d.deviceUpdateGen then 16 else 0) = (2 : Nat) := by
    rcases consistent with rfl | rfl <;> simp
  have rn : nlaTotal (d.ifname.length + 1) + 216 ≤ 3776 := by
    unfold devicePrefixSpace NLMSG_GOODSIZE at fits
    omega
  have rname : ¬ 3732 < nlaTotal (d.ifname.length + 1) := by omega
  have r36 : ¬ 3732 - nlaTotal (d.ifname.length + 1) < 36 := by omega
  have r72 : ¬ 3696 - nlaTotal (d.ifname.length + 1) < 36 := by omega
  have n2 : nlaTotal 2 = 8 := rfl
  have n4 : nlaTotal 4 = 8 := rfl
  have n32 : nlaTotal 32 = 36 := rfl
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  have branchRun (decision : Decision) (outcome : Bool) (w : World) :
      (branch decision outcome : Leanux.M Bool).run w =
        .ok (outcome, {w with ambient := {w.ambient with steps := w.ambient.steps.push {decision, outcome, netRx := w.ambient.netRxSection}}}) := rfl
  have okbind {α β : Type} (x : α) (f : α → Except Stop β) :
      ((Except.ok x : Except Stop α) >>= f) = f x := rfl
  intro w device
  let common := mark (mark (mark (mark (mark (mark w.ambient
    .dumpNoHdr false) .dumpFirst true) .dumpPutPort false) .dumpPutFwmark false)
    .dumpPutIfindex false) .dumpPutIfname false
  cases identity : d.staticIdentity.hasIdentity with
  | false =>
    let before := mark common .dumpHasIdentity false
    let attrs := [("listen_port", toJson d.incomingPort), ("fwmark", toJson d.fwmark),
      ("ifindex", toJson d.ifindex), ("ifname", toJson d.ifname)]
    let skb : NlSkb := {room := 3732 - nlaTotal (d.ifname.length + 1)}
    have pre : ({w with ambient := before} : World).wg.dev = some d ∧ (2 : Nat) = 2 ∧
        attrs = deviceFixedAttrs d ∧ skb.room = NLMSG_GOODSIZE - devicePrefixSpace d + 4 ∧ skb.messages = [] := by
      refine ⟨device, rfl, ?_, ?_, rfl⟩
      · simp [attrs, deviceFixedAttrs, identity]
      · dsimp [skb, devicePrefixSpace, NLMSG_GOODSIZE]
        simp [identity]
        omega
    obtain ⟨q, final, run, resultEq, finalDevice⟩ :=
      ((Product.returns_iff _ _ _).mpr (hf 2 attrs skb)) {w with ambient := before} pre
    refine ⟨q, final, ?_, resultEq, finalDevice⟩
    simpa [socketDumpHeaderSource, first, identity, flags, NlSkb.put, nlmsgTotal,
      n2, n4, n32, Nat.sub_sub, rname, r36, r72, StateT.run_bind, branchRun, okbind,
      mark, before, common, attrs, skb] using run
  | true =>
    let before := mark (mark (mark common .dumpHasIdentity true) .dumpPutPrivate false) .dumpPutPublic false
    let attrs := [("listen_port", toJson d.incomingPort), ("fwmark", toJson d.fwmark),
      ("ifindex", toJson d.ifindex), ("ifname", toJson d.ifname)] ++
      [("private_key", toJson (hexKey d.staticIdentity.staticPrivate)),
       ("public_key", toJson (hexKey d.staticIdentity.staticPublic))]
    let skb : NlSkb := {room := 3732 - nlaTotal (d.ifname.length + 1) - 36 - 36}
    have pre : ({w with ambient := before} : World).wg.dev = some d ∧ (2 : Nat) = 2 ∧
        attrs = deviceFixedAttrs d ∧ skb.room = NLMSG_GOODSIZE - devicePrefixSpace d + 4 ∧ skb.messages = [] := by
      refine ⟨device, rfl, ?_, ?_, rfl⟩
      · simp [attrs, deviceFixedAttrs, identity]
      · dsimp [skb, devicePrefixSpace, NLMSG_GOODSIZE]
        simp [identity]
        omega
    obtain ⟨q, final, run, resultEq, finalDevice⟩ :=
      ((Product.returns_iff _ _ _).mpr (hf 2 attrs skb)) {w with ambient := before} pre
    refine ⟨q, final, ?_, resultEq, finalDevice⟩
    simpa [socketDumpHeaderSource, first, identity, flags, NlSkb.put, nlmsgTotal,
      n2, n4, n32, Nat.sub_sub, rname, r36, r72, StateT.run_bind, branchRun, okbind,
      mark, before, common, attrs, skb] using run

theorem socketDumpHeader_contract_native (d : Device) (ctx : DumpCtx) (prev : Nat)
    (finish : Nat → List (String × Json) → NlSkb → WG.M DumpCall) (result : DumpCall)
    (first : ctx.nextPeer = none) (consistent : prev = 0 ∨ prev = d.deviceUpdateGen)
    (fits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (hf : ∀ flags attrs skb, ⦃fun w => ⌜w.dev = some d ∧ flags = 2 ∧
        attrs = deviceFixedAttrs d ∧ skb.room = NLMSG_GOODSIZE - devicePrefixSpace d + 4 ∧ skb.messages = []⌝⦄
      finish flags attrs skb ⦃⇓ q w => ⌜q = result ∧ w.dev = some d⌝⦄) :
    Returns (socketDumpHeaderSource d ctx prev {} finish) (fun w => w.dev = some d)
      (fun q w => q = result ∧ w.dev = some d) := by
  have flags : (2 + if prev ≠ 0 ∧ prev ≠ d.deviceUpdateGen then 16 else 0) = (2 : Nat) := by
    rcases consistent with rfl | rfl <;> simp
  have rn : nlaTotal (d.ifname.length + 1) + 216 ≤ 3776 := by
    unfold devicePrefixSpace NLMSG_GOODSIZE at fits
    omega
  have rname : ¬ 3732 < nlaTotal (d.ifname.length + 1) := by omega
  have r36 : ¬ 3732 - nlaTotal (d.ifname.length + 1) < 36 := by omega
  have r72 : ¬ 3696 - nlaTotal (d.ifname.length + 1) < 36 := by omega
  have n2 : nlaTotal 2 = 8 := rfl
  have n4 : nlaTotal 4 = 8 := rfl
  have n32 : nlaTotal 32 = 36 := rfl
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  intro g ambient device
  let common := mark (mark (mark (mark (mark (mark ambient
    .dumpNoHdr false) .dumpFirst true) .dumpPutPort false) .dumpPutFwmark false)
    .dumpPutIfindex false) .dumpPutIfname false
  cases identity : d.staticIdentity.hasIdentity with
  | false =>
    let before := mark common .dumpHasIdentity false
    let attrs := [("listen_port", toJson d.incomingPort), ("fwmark", toJson d.fwmark),
      ("ifindex", toJson d.ifindex), ("ifname", toJson d.ifname)]
    let skb : NlSkb := {room := 3732 - nlaTotal (d.ifname.length + 1)}
    have pre : g.dev = some d ∧ (2 : Nat) = 2 ∧
        attrs = deviceFixedAttrs d ∧ skb.room = NLMSG_GOODSIZE - devicePrefixSpace d + 4 ∧ skb.messages = [] := by
      refine ⟨device, rfl, ?_, ?_, rfl⟩
      · simp [attrs, deviceFixedAttrs, identity]
      · dsimp [skb, devicePrefixSpace, NLMSG_GOODSIZE]
        simp [identity]
        omega
    obtain ⟨q, final, after, run, resultEq, finalDevice⟩ :=
      ((returns_iff _ _ _).mpr (hf 2 attrs skb)) g before pre
    refine ⟨q, final, after, ?_, resultEq, finalDevice⟩
    simpa [socketDumpHeaderSource, first, identity, flags, NlSkb.put, nlmsgTotal,
      n2, n4, n32, Nat.sub_sub, rname, r36, r72, branch, AmbientM.branch,
      mark, before, common, attrs, skb] using run
  | true =>
    let before := mark (mark (mark common .dumpHasIdentity true) .dumpPutPrivate false) .dumpPutPublic false
    let attrs := [("listen_port", toJson d.incomingPort), ("fwmark", toJson d.fwmark),
      ("ifindex", toJson d.ifindex), ("ifname", toJson d.ifname)] ++
      [("private_key", toJson (hexKey d.staticIdentity.staticPrivate)),
       ("public_key", toJson (hexKey d.staticIdentity.staticPublic))]
    let skb : NlSkb := {room := 3732 - nlaTotal (d.ifname.length + 1) - 36 - 36}
    have pre : g.dev = some d ∧ (2 : Nat) = 2 ∧
        attrs = deviceFixedAttrs d ∧ skb.room = NLMSG_GOODSIZE - devicePrefixSpace d + 4 ∧ skb.messages = [] := by
      refine ⟨device, rfl, ?_, ?_, rfl⟩
      · simp [attrs, deviceFixedAttrs, identity]
      · dsimp [skb, devicePrefixSpace, NLMSG_GOODSIZE]
        simp [identity]
        omega
    obtain ⟨q, final, after, run, resultEq, finalDevice⟩ :=
      ((returns_iff _ _ _).mpr (hf 2 attrs skb)) g before pre
    refine ⟨q, final, after, ?_, resultEq, finalDevice⟩
    simpa [socketDumpHeaderSource, first, identity, flags, NlSkb.put, nlmsgTotal,
      n2, n4, n32, Nat.sub_sub, rname, r36, r72, branch, AmbientM.branch,
      mark, before, common, attrs, skb] using run

/-- The single-peer body uses the original getter result, loop exit, cursor
reference guards and DATA construction. -/
theorem socketDumpPeer_contract (pid : PeerId) (d : Device) (ctx outCtx : DumpCtx)
    (room : Nat) (peer : PeerDumpAttrs) (more : Bool)
    (peers : d.peerList = [pid]) (first : ctx.nextPeer = none)
    (outFirst : outCtx.nextPeer = none)
    (hp : ∀ skb, ⦃fun w => ⌜w.dev = some d ∧
        skb.room = NLMSG_GOODSIZE - devicePrefixSpace d ∧ skb.messages = []⌝⦄
      getPeerDump pid ctx skb ⦃⇓ q w => ⌜w.dev = some d ∧
        q = ({ room }, outCtx, if more then .split peer else .complete peer)⌝⦄) :
    Returns (socketDumpPeerSource d ctx 2 (deviceFixedAttrs d)
      { room := NLMSG_GOODSIZE - devicePrefixSpace d + 4 }) (fun w => w.dev = some d)
      (fun q w => q = socketCallbackResult d outCtx room peer more ∧ w.dev = some d) := by
  have fits : ¬ NLMSG_GOODSIZE - devicePrefixSpace d + 4 < 4 := by omega
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark ambient .dumpNoPeersNest false)
    .dumpPeerListEmpty false) .dumpCursorSet false) .dumpPeerIter true
  obtain ⟨q, final, afterGetter, getter, finalDevice, value⟩ :=
    ((returns_iff _ _ _).mpr (hp {room := NLMSG_GOODSIZE - devicePrefixSpace d}))
      g before ⟨device, rfl, rfl⟩
  subst q
  cases more with
  | false =>
    let after := mark (mark (mark (mark (mark (mark (mark afterGetter
      .dumpGetPeerFail false) .dumpPeerIter false) .dumpOutRetZero true)
      .dumpOutNotDone false) .peerPutNull true) .dumpRetErr false) .dumpDone true
    refine ⟨socketCallbackResult d outCtx room peer false, final, after, ?_, rfl, finalDevice⟩
    simp [socketDumpPeerSource, peers, first, branch, AmbientM.branch,
      WG.orM, WG.andM, NlSkb.put, nlaTotal, fits, List.forIn_cons, List.forIn_nil,
      requireNotPending, before, mark] at getter ⊢
    rw [getter]
    dsimp only [bind, Except.bind]
    simp [outFirst, peerPut, branch, AmbientM.branch, after, mark, socketCallbackResult,
      StateT.run, StateT.bind, StateT.pure, StateT.lift, liftM, monadLift, MonadLift.monadLift,
      Pure.pure, Except.pure, Bind.bind, Except.bind, Functor.map, StateT.map,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  | true =>
    let after := mark (mark (mark (mark (mark (mark (mark afterGetter
      .dumpGetPeerFail true) .dumpOutRetZero true) .dumpOutNotDone true)
      .dumpOutHasCursor false) .peerPutNull true) .dumpRetErr false) .dumpDone false
    refine ⟨socketCallbackResult d outCtx room peer true, final, after, ?_, rfl, finalDevice⟩
    simp [socketDumpPeerSource, peers, first, branch, AmbientM.branch,
      WG.orM, WG.andM, NlSkb.put, nlaTotal, fits, List.forIn_cons, List.forIn_nil,
      requireNotPending, before, mark] at getter ⊢
    rw [getter]
    dsimp only [bind, Except.bind]
    simp [outFirst, peerPut, branch, AmbientM.branch, after, mark, socketCallbackResult,
      StateT.run, StateT.bind, StateT.pure, StateT.lift, liftM, monadLift, MonadLift.monadLift,
      Pure.pure, Except.pure, Bind.bind, Except.bind, Functor.map, StateT.map,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

theorem deviceDump_single_contract (pid : PeerId) (d : Device) (ctx outCtx : DumpCtx)
    (prevSeq room : Nat) (peer : PeerDumpAttrs) (more : Bool)
    (peers : d.peerList = [pid]) (first : ctx.nextPeer = none)
    (outFirst : outCtx.nextPeer = none)
    (consistent : prevSeq = 0 ∨ prevSeq = d.deviceUpdateGen)
    (fits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (hp : Returns (getPeerDump pid ctx { room := NLMSG_GOODSIZE - devicePrefixSpace d })
      (fun w => w.dev = some d)
      (fun q w => w.dev = some d ∧ q =
        ({ room }, outCtx, if more then .split peer else .complete peer))) :
    Returns (wgGetDeviceDump ctx prevSeq {}) (fun w => w.dev = some d)
      (fun q w => q = socketCallbackResult d outCtx room peer more ∧ w.dev = some d) := by
  have hpAny (skb : NlSkb) :
      ⦃fun w => ⌜w.dev = some d ∧ skb.room = NLMSG_GOODSIZE - devicePrefixSpace d ∧ skb.messages = []⌝⦄
      getPeerDump pid ctx skb ⦃⇓ q w => ⌜w.dev = some d ∧ q =
        ({ room }, outCtx, if more then .split peer else .complete peer)⌝⦄ := by
    apply (returns_iff _ _ _).mp
    intro w ambient ⟨hd, hr, hm⟩
    have heq : skb = { room := NLMSG_GOODSIZE - devicePrefixSpace d } := by
      cases skb; simp_all
    rw [heq]
    exact hp w ambient hd
  have ht := socketDumpPeer_contract pid d ctx outCtx room peer more peers first outFirst hpAny
  have hh := socketDumpHeader_contract_native d ctx prevSeq (socketDumpPeerSource d ctx)
    (socketCallbackResult d outCtx room peer more) first consistent fits
  have body : Returns (deviceDumpSource d ctx prevSeq {}) (fun w => w.dev = some d)
      (fun q w => q = socketCallbackResult d outCtx room peer more ∧ w.dev = some d) := by
    rw [socketDump_source]
    apply hh
    intro flags attrs skb
    apply (returns_iff _ _ _).mp
    intro w ambient ⟨hd, hf, ha, hr, hm⟩
    have heq : skb = { room := NLMSG_GOODSIZE - devicePrefixSpace d + 4 } := by
      cases skb; simp_all
    subst flags; subst attrs; subst skb
    exact ht w ambient hd
  have hg : Returns getDev (fun w => w.dev = some d)
      (fun q w => q = d ∧ w.dev = some d) := by
    intro g ambient device
    refine ⟨d, g, ambient, ?_, rfl, device⟩
    simp [getDev, device]
    rfl
  rw [wgGetDeviceDump_source]
  apply returns_bind _ _ hg
  intro q w ambient ⟨heq, hd⟩
  subst q
  exact body w ambient hd

end Leanux.Proofs.WG.Config
