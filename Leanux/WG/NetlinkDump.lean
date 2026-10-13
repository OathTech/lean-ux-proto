import Leanux.WG.Netlink

/-!
# drivers/net/wireguard/netlink.c — WG_CMD_GET_DEVICE, and the netlink dump
loop it runs in (net/netlink/af_netlink.c)

The dump half of `Leanux/WG/Netlink.lean` (W1+W2 execution plan, step 0), with
W2's put model and chunk machine (docs/2026-10-06-w1-w2-netlink.md, 4.3):
every `nla_put` reserves its `nla_total_size` from the chunk's room and fails
when the room is short (lib/nlattr.c:1094), a nest start is a 4-byte put
whose cancel restores the room, and the netlink core runs one dump call per
chunk (`netlink_dump`: inside the `sendmsg` that starts the dump, then inside
every `recvmsg` while `cb_running`). The per-socket state is
`Leanux.WG.NlSock` (`Kernel.nlSock7`, `Kernel.nlSock8`).
-/

namespace Leanux.WG
open Leanux Lean

/-! ## WG_CMD_GET_DEVICE -/

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

def hexKey (k : Key) : String :=
  String.ofList (k.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit b.toNat])

/-- `len` bytes of `n`, big-endian, as lowercase hex. -/
def hexBE (n len : Nat) : String :=
  String.ofList ((List.range len).reverse.flatMap fun i =>
    let b := n / 256 ^ i % 256
    [hexDigit (b / 16), hexDigit b])

/-! ### The put model (design section 2.5) -/

/-- `NLMSG_GOODSIZE` = `SKB_WITH_OVERHEAD(PAGE_SIZE)` with
    `sizeof(struct skb_shared_info)` 320 (the reference vmlinux): every dump
    chunk's room, since the guest receives exactly that many bytes (4.1). -/
def NLMSG_GOODSIZE : Nat := 3776

/-- `nla_total_size(len)` = `NLA_ALIGN(NLA_HDRLEN + len)`. -/
def nlaTotal (len : Nat) : Nat := (4 + len + 3) / 4 * 4

/-- `nlmsg_total_size(payload)` = `NLMSG_ALIGN(NLMSG_HDRLEN + payload)`. -/
def nlmsgTotal (payload : Nat) : Nat := (16 + payload + 3) / 4 * 4

/-- `nla_put`'s test (lib/nlattr.c:1094-1097; `nla_reserve` :969): true,
    the failure, iff the tailroom is below the attribute's total size; else
    the bytes are reserved. -/
def NlSkb.put (skb : NlSkb) (n : Nat) : Bool × NlSkb :=
  if skb.room < n then (true, skb) else (false, { skb with room := skb.room - n })

/-- get_allowedips (netlink.c:75-94), after wg_allowedips_read_node: the
    IP's nest, cidr, family and address; a failed put cancels the nest
    (:90, the room restored) and returns `-EMSGSIZE` (`none`). -/
def getAllowedips (skb0 : NlSkb) (family masked cidr : Nat) : M (NlSkb × Option Json) := do
  let (fail, skb) := skb0.put (nlaTotal 0)
  if ← branch .getAipNoNest fail then return (skb0, none)
  let (fail, skb) := skb.put (nlaTotal 1)
  if ← branch .getAipPutCidr fail then return (skb0, none)
  let (fail, skb) := skb.put (nlaTotal 2)
  if ← branch .getAipPutFamily fail then return (skb0, none)
  let inet6 ← branch .getAipFamily6 (family == 6)   -- sizeof(in6_addr) or sizeof(in_addr)
  let (fail, skb) := skb.put (nlaTotal (if inet6 then 16 else 4))
  if ← branch .getAipPutAddr fail then return (skb0, none)
  return (skb, some (Json.mkObj [("family", toJson family), ("addr", toJson (hexBE masked (if inet6 then 16 else 4))),
    ("cidr", toJson cidr)]))

/-- A `struct timespec64` (16 bytes: `tv_sec`, `tv_nsec`, little-endian
    s64) as the `__kernel_timespec` the dump puts (netlink.c:124-138). -/
def timespec (ts : List UInt8) : List Int :=
  let s64 (bs : List UInt8) : Int :=
    let u : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
    if u ≥ 2 ^ 63 then (u : Int) - (2 ^ 64 : Int) else (u : Int)
  [s64 (ts.take 8), s64 ((ts.drop 8).take 8)]

/-- `get_peer`'s result: the peer complete (0), its allowed IPs continued
    in the next chunk (`-EMSGSIZE` after `nla_nest_end`, the cursor set), or
    the nest cancelled (`err:`, `-EMSGSIZE`, nothing of the peer in the chunk). -/
inductive PeerDump where
  | complete (peer : PeerDumpAttrs)
  | split (peer : PeerDumpAttrs)
  | cancelled

/-- get_peer (netlink.c:105-197) in the chunk `skb0` with the dump context
    `ctx`. The fixed part is put on a fresh cursor only (:123, read before
    anything else of the peer: a stale cursor skips it, 2.4); the cursors
    reset only on completion (:191-192). -/
def getPeerDump (pid : PeerId) (ctx0 : DumpCtx) (skb0 : NlSkb) : M (NlSkb × DumpCtx × PeerDump) := do
  let p ← getPeer pid
  let mut ctx := ctx0
  -- peer_nest = nla_nest_start(skb, 0); allowedips_node = ctx->next_allowedip
  let (fail, skb) := skb0.put (nlaTotal 0)
  if ← branch .getPeerNoNest fail then return (skb0, ctx, .cancelled)
  let mut node := ctx.nextAllowedip
  let mut skb := skb
  let pubkey := hexKey p.remoteStatic
  let mut attrs : List (String × Json) := [("public_key", toJson pubkey)]
  let (fail, s) := skb.put (nlaTotal 32); skb := s
  if ← branch .getPeerPubkeyFail fail then return (skb0, ctx, .cancelled)
  if ← branch .getPeerFirst node.isNone then
    let (fail, s) := skb.put (nlaTotal 32); skb := s
    if ← branch .getPeerPskFail fail then return (skb0, ctx, .cancelled)
    -- the `||` chain of :137-146: each put runs only if the earlier ones succeeded
    let (fail, s) := skb.put (nlaTotal 16); skb := s
    if ← branch .getPeerPutHandshake fail then return (skb0, ctx, .cancelled)
    let (fail, s) := skb.put (nlaTotal 2); skb := s
    if ← branch .getPeerPutKeepalive fail then return (skb0, ctx, .cancelled)
    let (fail, s) := skb.put (nlaTotal 8); skb := s
    if ← branch .getPeerPutTx fail then return (skb0, ctx, .cancelled)
    let (fail, s) := skb.put (nlaTotal 8); skb := s
    if ← branch .getPeerPutRx fail then return (skb0, ctx, .cancelled)
    let (fail, s) := skb.put (nlaTotal 4); skb := s
    if ← branch .getPeerPutProto fail then return (skb0, ctx, .cancelled)
    attrs := attrs ++ [("preshared_key", toJson (hexKey p.presharedKey)),
      ("last_handshake", toJson (timespec p.walltimeLastHandshake)), ("keepalive", toJson p.persistentKeepaliveInterval),
      ("tx_bytes", toJson p.txBytes), ("rx_bytes", toJson p.rxBytes), ("protocol_version", toJson 1)]
    -- the whole sockaddr is put (:150-156): for IPv6 its flowinfo and
    -- scope_id too (W1 3.2)
    let family := p.endpoint.map (·.family) |>.getD 0
    let mut epFail := false
    if ← branch .getPeerEp4 (family == AF_INET) then
      let (fail, s) := skb.put (nlaTotal 16); skb := s; epFail := fail
    else if ← branch .getPeerEp6 (family == AF_INET6) then
      let (fail, s) := skb.put (nlaTotal 28); skb := s; epFail := fail
    if ← branch .getPeerEpFail epFail then return (skb0, ctx, .cancelled)
    attrs := attrs ++ match p.endpoint with
      | some e =>
        let v4 := e.family == AF_INET
        [("endpoint", Json.mkObj ([("family", toJson (if v4 then 4 else 6)),
          ("addr", toJson (hexBE e.addr (if v4 then 4 else 16))), ("port", toJson e.port)] ++
          (if v4 then [] else [("flowinfo", toJson e.flowinfo), ("scope_id", toJson e.scope)])))]
      | none => []
    node := p.allowedipsList.head?   -- list_first_entry_or_null
  let done (ctx : DumpCtx) (attrs : List (String × Json)) : DumpCtx × PeerDump :=
    ({ ctx with nextAllowedip := none, allowedipsSeq := 0 }, .complete { publicKey := pubkey, attrs })
  if ← branch .getPeerNoAips node.isNone then
    -- no_allowedips: nla_nest_end(peer_nest), both cursors reset
    let (c, r) := done ctx attrs
    return (skb, c, r)
  let seq := (← getDev).peerAllowedips.seq
  if ← branch .getPeerSeqUnset (ctx.allowedipsSeq == 0) then
    ctx := { ctx with allowedipsSeq := seq }
  else if ← branch .getPeerSeqChanged (ctx.allowedipsSeq != seq) then
    let (c, r) := done ctx attrs
    return (skb, c, r)
  let (fail, s) := skb.put (nlaTotal 0); skb := s
  if ← branch .getPeerAipsNestFail fail then return (skb0, ctx, .cancelled)
  -- list_for_each_entry_from(allowedips_node, &peer->allowedips_list): the
  -- node is dereferenced here, after the seq test (:175); an unchanged seq
  -- means it is still on the list
  let some start := node | invariant "unreachable"
  let rest := p.allowedipsList.dropWhile (· != start)
  if rest.isEmpty then invariant "a stale allowed-IPs cursor with an unchanged sequence (2.4)"
  let mut ips : Array Json := #[]
  for id in rest do
    _ ← branch .getPeerAipIter true
    let (family, masked, cidr) ← readNode (← getNode id)
    let (s, ip) ← getAllowedips skb family masked cidr
    skb := s
    if ← branch .getPeerAipFail ip.isNone then
      -- nla_nest_end both; ctx->next_allowedip = node; return -EMSGSIZE
      return (skb, { ctx with nextAllowedip := some id },
        .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr ips)], split := true })
    ips := ips.push ip.get!
  _ ← branch .getPeerAipIter false
  let (c, r) := done ctx (attrs ++ [("allowed_ips", Json.arr ips)])
  return (skb, c, r)

/-- wg_get_device_done (netlink.c:304-312): the device reference and the
    cursor peer's. -/
def wgGetDeviceDone (ctx : DumpCtx) : M Unit := do
  _ ← branch .getDoneHasWg ctx.hasWg
  peerPut ctx.nextPeer

/-- One dump call's outcome: `ret` as the C returns it (0 done, positive
    `skb->len` for more), the chunk, the context and `cb->prev_seq`. -/
structure DumpCall where
  ret : Int
  skb : NlSkb
  ctx : DumpCtx
  prevSeq : Nat

/-- wg_get_device_dump (netlink.c:210-302): one call, one chunk (`skb0`,
    fresh from `netlink_dump`). The device part goes in while
    `ctx->next_peer` is `NULL` (:231-252), then the peers from the cursor on
    (:269-276), each put reserving from the room. A header or device-part
    put that fails is unreachable with 3776 bytes of room (2.3): the mirror
    stops rather than model the `-EMSGSIZE` return. -/
def wgGetDeviceDump (ctx0 : DumpCtx) (prevSeq0 : Nat) (skb0 : NlSkb) : M DumpCall := do
  let d ← getDev
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
  if ← orM (branch .dumpPeerListEmpty d.peerList.isEmpty)
      (andM (branch .dumpCursorSet ctx.nextPeer.isSome) (do branch .dumpCursorDead (← cursorDead))) then
    skb := nestStart   -- nla_nest_cancel(skb, peers_nest); goto out
    peers := none
  else
    -- list_prepare_entry / list_for_each_entry_continue: from the peer
    -- after the cursor (the last completed one), or the first
    let fromPeers := match ctx.nextPeer with
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
  if ← andM (branch .dumpOutRetZero (ret == 0))
      (andM (branch .dumpOutNotDone !done) (branch .dumpOutHasCursor nextCursor.isSome)) then
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

/-! ### The netlink dump loop (af_netlink.c), per socket -/

/-- `INT_MAX`: `dump_done_errno` while the dump runs. -/
def INT_MAX : Int := 2147483647

def getNlSock (fd : Nat) : M NlSock := do
  let k ← getK
  return if fd == 8 then k.nlSock8 else k.nlSock7

def setNlSock (fd : Nat) (s : NlSock) : M Unit :=
  modifyK fun k => if fd == 8 then { k with nlSock8 := s } else { k with nlSock7 := s }

/-- `netlink_dump` (af_netlink.c:2255-2383): a fresh chunk, the dump
    callback while `dump_done_errno > 0`, then either the chunk queued
    without `NLMSG_DONE` (more to dump, or fewer than 20 bytes of room) or
    `NLMSG_DONE` appended, the chunk queued, `done` run and `cb_running`
    cleared. -/
def netlinkDump (fd : Nat) : M Unit := do
  let mut sock ← getNlSock fd
  let mut skb : NlSkb := {}
  if sock.dumpDoneErrno > 0 then
    let r ← wgGetDeviceDump sock.ctx sock.prevSeq skb
    -- `-EMSGSIZE` with data in the chunk (:2333-2334) is unreachable for
    -- WireGuard (2.3): the callback cancels its header before returning it
    skb := r.skb
    sock := { sock with ctx := r.ctx, prevSeq := r.prevSeq, dumpDoneErrno := r.ret }
  if sock.dumpDoneErrno > 0 || skb.room < nlmsgTotal 4 then
    setNlSock fd { sock with queue := sock.queue ++ [skb] }
    return
  -- netlink_dump_done (:2225-2250): NLMSG_DONE carrying dump_done_errno,
  -- NLM_F_MULTI (the consistency flag never set here, 2.4)
  skb := { skb with room := skb.room - nlmsgTotal 4, messages := skb.messages ++ [.done 2 sock.dumpDoneErrno] }
  setNlSock fd { sock with queue := sock.queue ++ [skb] }
  wgGetDeviceDone sock.ctx   -- cb->done (:2370)
  let after ← getNlSock fd
  setNlSock fd { after with cbRunning := false }

/-- `__netlink_dump_start` (af_netlink.c:2386-2460) for a `WG_CMD_GET_DEVICE`
    request on socket `fd`: `-EBUSY` while the socket's dump runs (:2406,
    queued as an acknowledgement behind the pending chunk; no WireGuard code
    runs, so the operation is outside the domain [AGENT, coordinator
    2026-10-12: the WireGuard boundary]); else `wg_get_device_start`
    (netlink.c:199-208; its error is acknowledged, :2556) and the first dump
    call inside the `sendmsg` (:2437-2440). -/
def netlinkDumpStart (fd : Nat) (ref : DeviceRef) : M Unit := do
  let sock ← getNlSock fd
  if sock.cbRunning then
    unsupported "a dump start while the socket's dump runs (-EBUSY, af_netlink.c:2406): no WireGuard code runs"
  let wg ← lookupInterface ref
  if ← branch .getStartErr (wg matches .error _) then
    let .error e := wg | invariant "unreachable"
    -- `cb` is zeroed (:2417) before `start` (:2431), so the context and
    -- `prev_seq` are gone on a start error too (audit, the transport note)
    setNlSock fd { sock with queue := sock.queue ++ [{ messages := [.error e] }], ctx := {}, prevSeq := 0 }
    return
  -- cb zeroed (:2422), then cb_running and dump_done_errno = INT_MAX (:2436-2437)
  setNlSock fd { sock with cbRunning := true, dumpDoneErrno := INT_MAX, prevSeq := 0, ctx := { hasWg := true } }
  netlinkDump fd

/-- `netlink_recvmsg` (af_netlink.c:1898-1990) on socket `fd`: one queued
    chunk or acknowledgement (`none`: `-EAGAIN`, nothing queued), then the
    next dump call while `cb_running` (:1974-1980; the receive queue is far
    below half `sk_rcvbuf`, 4.9). -/
def netlinkRecvmsg (fd : Nat) : M (Option (List NlMessage)) := do
  let sock ← getNlSock fd
  match sock.queue with
  | [] => return none
  | skb :: rest =>
    setNlSock fd { sock with queue := rest }
    if (← getNlSock fd).cbRunning then netlinkDump fd
    return some skb.messages

/-- `wg_get` (op 9): the guest drains the dump to `NLMSG_DONE` in one
    operation and the harness coalesces the chunks into the canonical
    device state (4.5): the device part from the first chunk (a repeated one
    must be identical), the peers in order, a split peer's allowed IPs
    merged with its continuation, `allowed_ips: []` for a peer dumped
    without the nest. Within one operation nothing changes
    `device_update_gen` or the allowed-IPs sequence, so a continuation
    without allowed IPs or `NLM_F_DUMP_INTR` is a mirror defect. -/
def coalesce (ms : List NlMessage) : M (Except Int Json) := do
  if let [.error e] := ms then return .error e
  let mut device : Option (List (String × Json)) := none
  let mut peers : Array PeerDumpAttrs := #[]
  let mut doneErr : Option Int := none
  for m in ms do
    match m with
    | .error _ => invariant "op 9: an acknowledgement among the dump's chunks"
    | .done flags e =>
      if flags != 2 then invariant "op 9: NLMSG_DONE with the consistency flag"
      doneErr := some e
    | .data flags part ps =>
      if flags != 2 then invariant "op 9: NLM_F_DUMP_INTR within one operation"
      if !part.isEmpty then
        match device with
        | none => device := some part
        | some first =>
          if (Json.mkObj first).compress != (Json.mkObj part).compress then
            invariant "op 9: a repeated device part differs"
      let some ps := ps | continue   -- the nest cancelled: no peers in this chunk
      let mut first := true
      for p in ps do
        let continued := first && peers.size > 0 && peers.back!.split && peers.back!.publicKey == p.publicKey
        first := false
        if continued then
          let last := peers.back!
          let extra := p.attrs.filter fun (k, _) => k != "public_key" && k != "allowed_ips"
          if !extra.isEmpty then invariant "op 9: a continued peer repeats attributes"
          let some (Json.arr more) := p.attrs.lookup "allowed_ips" | invariant "op 9: a continued peer without allowed IPs"
          let merged := last.attrs.map fun (k, v) =>
            if k == "allowed_ips" then
              (k, match v with | Json.arr a => Json.arr (a ++ more) | v => v)
            else (k, v)
          peers := peers.pop.push { last with attrs := merged, split := p.split }
        else
          let withIps := if p.attrs.any (·.1 == "allowed_ips") then p.attrs
            else p.attrs ++ [("allowed_ips", Json.arr #[])]
          peers := peers.push { p with attrs := withIps }
  let some e := doneErr | invariant "op 9: the dump ended without NLMSG_DONE"
  if e != 0 then return .error e
  let some part := device | invariant "op 9: no device part"
  return .ok (Json.mkObj (part ++ [("peers", Json.arr (peers.map fun p => Json.mkObj p.attrs))]))

/-- A WG_CMD_GET_DEVICE dump on the fixture's socket (op 9): the start and
    the first dump call inside the `sendmsg`, then receives until the
    `NLMSG_DONE` (or the acknowledgement of a start error), each running the
    next dump call; the chunks coalesced to the canonical device state. -/
def wgGetDevice (ref : DeviceRef) : M (Except Int Json) := do
  netlinkDumpStart 7 ref
  let mut messages : Array NlMessage := #[]
  let mut finished := false
  for _ in [0:4096] do
    if finished then break
    let some ms ← netlinkRecvmsg 7 | invariant "op 9: nothing queued before the dump finished"
    for m in ms do
      messages := messages.push m
      match m with
      | .done .. | .error _ => finished := true
      | .data .. => pure ()
  if !finished then invariant "op 9: the dump did not finish"
  coalesce messages.toList

end Leanux.WG
