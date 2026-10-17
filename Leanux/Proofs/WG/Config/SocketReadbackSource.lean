import Leanux.Proofs.WG.Config.SocketReadbackScanSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def socketDumpHeaderSource (d : Device) (ctx0 : DumpCtx) (prevSeq0 : Nat) (skb0 : NlSkb)
    (finish : Nat → List (String × Json) → NlSkb → M DumpCall) : M DumpCall := do
  let seq := d.deviceUpdateGen   -- cb->seq (:222)
  let mut ctx := ctx0
  let mut nextCursor := ctx.nextPeer
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

def socketDumpPeerSource (d : Device) (ctx0 : DumpCtx) (flags : Nat) (device : List (String × Json)) (skb : NlSkb) : M DumpCall := do
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
  let cursorDead : M Bool := do
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
    (finish : Nat → List (String × Json) → NlSkb → M DumpCall) (result : DumpCall)
    (first : ctx.nextPeer = none) (consistent : prev = 0 ∨ prev = d.deviceUpdateGen)
    (fits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (hf : ∀ flags attrs skb, ⦃fun w => ⌜w.k.wg = some d ∧ flags = 2 ∧
        attrs = deviceFixedAttrs d ∧ skb.room = NLMSG_GOODSIZE - devicePrefixSpace d + 4 ∧ skb.messages = []⌝⦄
      finish flags attrs skb ⦃⇓ q w => ⌜q = result ∧ w.k.wg = some d⌝⦄) :
    Returns (socketDumpHeaderSource d ctx prev {} finish) (fun w => w.k.wg = some d)
      (fun q w => q = result ∧ w.k.wg = some d) := by
  have flags : (2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0) = (2 : Nat) := by
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
  have hb := branch_state_returns (fun k => k.wg = some d)
  rw [returns_iff]
  cases identity : d.staticIdentity.hasIdentity
  all_goals simp [socketDumpHeaderSource, first, identity, flags, bind_assoc,
    NlSkb.put, nlmsgTotal, n2, n4, n32, Nat.sub_sub, rname, r36, r72]
  all_goals mvcgen [hf, hb, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [deviceFixedAttrs, devicePrefixSpace, identity, NLMSG_GOODSIZE, nlaTotal]
  all_goals omega

/-- The single-peer body uses the original getter result, loop exit, cursor
reference guards and DATA construction. -/
theorem socketDumpPeer_contract (pid : PeerId) (d : Device) (ctx outCtx : DumpCtx)
    (room : Nat) (peer : PeerDumpAttrs) (more : Bool)
    (peers : d.peerList = [pid]) (first : ctx.nextPeer = none)
    (outFirst : outCtx.nextPeer = none)
    (hp : ∀ skb, ⦃fun w => ⌜w.k.wg = some d ∧
        skb.room = NLMSG_GOODSIZE - devicePrefixSpace d ∧ skb.messages = []⌝⦄
      getPeerDump pid ctx skb ⦃⇓ q w => ⌜w.k.wg = some d ∧
        q = ({ room }, outCtx, if more then .split peer else .complete peer)⌝⦄) :
    Returns (socketDumpPeerSource d ctx 2 (deviceFixedAttrs d)
      { room := NLMSG_GOODSIZE - devicePrefixSpace d + 4 }) (fun w => w.k.wg = some d)
      (fun q w => q = socketCallbackResult d outCtx room peer more ∧ w.k.wg = some d) := by
  have fits : ¬ NLMSG_GOODSIZE - devicePrefixSpace d + 4 < 4 := by omega
  simp [socketDumpPeerSource, peers, first, branch, WG.orM, WG.andM, bind_assoc,
    NlSkb.put, nlaTotal, fits, List.forIn_cons, List.forIn_nil, requireNotPending]
  apply returns_bind (Q := fun _ w => w.k.wg = some d)
  · rw [returns_iff]; mvcgen
  · intro _
    apply returns_bind (Q := fun _ w => w.k.wg = some d)
    · rw [returns_iff]; mvcgen
    · intro _
      apply returns_bind (Q := fun _ w => w.k.wg = some d)
      · rw [returns_iff]; mvcgen
      · intro _
        apply returns_bind (Q := fun _ w => w.k.wg = some d)
        · rw [returns_iff]; mvcgen
        · intro _
          have hg : Returns (getPeerDump pid ctx { room := NLMSG_GOODSIZE - devicePrefixSpace d })
              (fun w => w.k.wg = some d)
              (fun q w => w.k.wg = some d ∧ q =
                ({ room }, outCtx, if more then .split peer else .complete peer)) := by
            rw [returns_iff]
            intro w hd
            exact hp _ w ⟨hd, rfl, rfl⟩
          apply returns_bind _ _ hg
          intro q
          rw [returns_iff]
          intro w h
          obtain ⟨hd, rfl⟩ := h
          cases more
          all_goals simp [List.forIn_cons, List.forIn_nil, outFirst, socketCallbackResult, bind_assoc]
          all_goals mvcgen [peerPut, branch]
          all_goals simp_all

theorem deviceDump_single_contract (pid : PeerId) (d : Device) (ctx outCtx : DumpCtx)
    (prevSeq room : Nat) (peer : PeerDumpAttrs) (more : Bool)
    (peers : d.peerList = [pid]) (first : ctx.nextPeer = none)
    (outFirst : outCtx.nextPeer = none)
    (consistent : prevSeq = 0 ∨ prevSeq = d.deviceUpdateGen)
    (fits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (hp : Returns (getPeerDump pid ctx { room := NLMSG_GOODSIZE - devicePrefixSpace d })
      (fun w => w.k.wg = some d)
      (fun q w => w.k.wg = some d ∧ q =
        ({ room }, outCtx, if more then .split peer else .complete peer))) :
    Returns (wgGetDeviceDump ctx prevSeq {}) (fun w => w.k.wg = some d)
      (fun q w => q = socketCallbackResult d outCtx room peer more ∧ w.k.wg = some d) := by
  have hpAny (skb : NlSkb) :
      ⦃fun w => ⌜w.k.wg = some d ∧ skb.room = NLMSG_GOODSIZE - devicePrefixSpace d ∧ skb.messages = []⌝⦄
      getPeerDump pid ctx skb ⦃⇓ q w => ⌜w.k.wg = some d ∧ q =
        ({ room }, outCtx, if more then .split peer else .complete peer)⌝⦄ := by
    intro w ⟨hd, hr, hm⟩
    have heq : skb = { room := NLMSG_GOODSIZE - devicePrefixSpace d } := by
      cases skb; simp_all
    rw [heq]
    exact (returns_iff _ _ _).mp hp w hd
  have ht := socketDumpPeer_contract pid d ctx outCtx room peer more peers first outFirst hpAny
  have hh := socketDumpHeader_contract d ctx prevSeq (socketDumpPeerSource d ctx)
    (socketCallbackResult d outCtx room peer more) first consistent fits
  have body : Returns (deviceDumpSource d ctx prevSeq {}) (fun w => w.k.wg = some d)
      (fun q w => q = socketCallbackResult d outCtx room peer more ∧ w.k.wg = some d) := by
    rw [socketDump_source]
    apply hh
    intro flags attrs skb w ⟨hd, hf, ha, hr, hm⟩
    have heq : skb = { room := NLMSG_GOODSIZE - devicePrefixSpace d + 4 } := by
      cases skb; simp_all
    subst flags; subst attrs; subst skb
    exact (returns_iff _ _ _).mp ht w hd
  have hg : Returns getDev (fun w => w.k.wg = some d)
      (fun q w => q = d ∧ w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [getDev, getK, invariant]
    all_goals simp_all
  rw [wgGetDeviceDump_source]
  apply returns_bind _ _ hg
  intro q w ⟨heq, hd⟩
  subst q
  exact body w hd

end Leanux.Proofs.WG.Config
