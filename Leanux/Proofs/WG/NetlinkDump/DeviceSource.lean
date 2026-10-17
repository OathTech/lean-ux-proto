import Leanux.WG.NetlinkDump

/-! Literal device-chunk serialization and peer-walk cuts. The header only uses
saved device scalars and records; the tail retains every actual peer access. -/
namespace Leanux.Proofs.WG.NetlinkDump
open Leanux Leanux.WG Lean
set_option maxHeartbeats 1000000

def deviceDumpHeaderSource (d : Device) (ctx : DumpCtx) (prevSeq0 : Nat) (skb0 : NlSkb) :
    WG.M (NlSkb × Nat × List (String × Json)) := do
  let seq := d.deviceUpdateGen
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
  return (skb, flags, device)

def deviceDumpTailSource (d : Device) (ctx0 : DumpCtx) (skb0 : NlSkb)
    (flags : Nat) (device : List (String × Json)) : WG.M DumpCall := do
  let seq := d.deviceUpdateGen
  let mut ctx := ctx0
  let mut nextCursor := ctx.nextPeer
  let mut skb := skb0
  let nestStart := skb
  let ret : Int := 0
  let mut done := true
  let mut peers : Option (Array PeerDumpAttrs) := some #[]
  let cursorDead : WG.M Bool := do
    let some pid := ctx.nextPeer | invariant "unreachable"
    return (← getPeer pid).isDead
  if ← Leanux.WG.orM (branch .dumpPeerListEmpty d.peerList.isEmpty)
      (Leanux.WG.andM (branch .dumpCursorSet ctx.nextPeer.isSome) (do branch .dumpCursorDead (← cursorDead))) then
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
  if ← Leanux.WG.andM (branch .dumpOutRetZero (ret == 0))
      (Leanux.WG.andM (branch .dumpOutNotDone !done) (branch .dumpOutHasCursor nextCursor.isSome)) then
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


private theorem source_if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p] (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem source_unsupported_bind (s : String) (f : α → Leanux.M β) :
    (unsupported s >>= f) = (unsupported s : Leanux.M β) := rfl
private theorem source_unsupported_bind_wg (s : String) (f : α → WG.M β) :
    (unsupported s >>= f) = (unsupported s : WG.M β) := rfl
private theorem source_bind_congr {m : Type → Type} [Monad m] (a : m α) (f g : α → m β) (h : ∀ x, f x = g x) :
    (a >>= f) = (a >>= g) := congrArg (fun k => a >>= k) (funext h)

theorem wgGetDeviceDump_source (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    wgGetDeviceDump ctx prevSeq skb = (do
      let d ← getDev
      let (s, flags, attrs) ← deviceDumpHeaderSource d ctx prevSeq skb
      deviceDumpTailSource d ctx s flags attrs) := by
  simp only [wgGetDeviceDump, deviceDumpHeaderSource, bind_assoc, pure_bind, source_if_bind, source_unsupported_bind_wg]
  repeat' first
    | rfl
    | (apply source_bind_congr; intro x)
    | split
    | simp only [bind_assoc, pure_bind, source_if_bind, source_unsupported_bind_wg]

end Leanux.Proofs.WG.NetlinkDump
