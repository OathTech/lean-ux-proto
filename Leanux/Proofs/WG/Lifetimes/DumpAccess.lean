import Leanux.Proofs.Framing.WGDump
import Leanux.Proofs.WG.NetlinkDump.DeviceSource
import Leanux.Proofs.WG.Lifetimes.ConfigurationLeaves
import Leanux.Proofs.Logged.PrefixLoops

/-! The complete dump family observes actual resolved peer identities. Socket
records and scalar cursor labels are not object accesses; each demanded cursor
or peer getter is observed at its source site. Saved serialization fields have
no intervening resident mutation. Queueing, reference replacement, early returns,
finite exhaustion and every Stop retain their original order and reached history. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Lean Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.NetlinkDump
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
open DumpKernelComposition

def DumpStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, dumpView v = dumpView w → I h w → I h v

theorem allocationDumpStable : DumpStable AllocationInv := by
  intro h w v he hi
  have hid := congrArg (fun k => identityView {w with k}) he
  have hmeta := congrArg (fun k => allocationMetadata {w with k}) he
  apply hi.congr
  · unfold identityView Peers.snapshot keypairResidents packetResidents at hid ⊢
    simpa [dumpView, dumpKernel] using hid
  · unfold allocationMetadata deviceAllocationMetadata at hmeta ⊢
    simpa [dumpView, dumpKernel] using hmeta

theorem dumpLift_preserves (c : AmbientContracts I) (stable : DumpStable I)
    (a : M α) (ha : SameDumpKernel a) : PrefixPreserves I LifetimeEvent.Safe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a c.safe
  intro h w x v hi hr
  exact stable h w v (ha w x v hr) hi

def getPeerDumpPrefix (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    MixedM (NlSkb × DumpCtx × PeerDump) := do
  let p ← getPeerMixed pid
  liftPrefix (getPeerDumpTailSource p ctx skb)

def wgGetDeviceDonePrefix (ctx : DumpCtx) : MixedM Unit := do
  _ ← rxBranch .getDoneHasWg ctx.hasWg
  peerPutMixed ctx.nextPeer

def deviceDumpTailPrefix (d : Device) (ctx0 : DumpCtx) (skb0 : NlSkb)
    (flags : Nat) (device : List (String × Json)) : MixedM DumpCall := do
  let seq := d.deviceUpdateGen
  let mut ctx := ctx0
  let mut nextCursor := ctx.nextPeer
  let mut skb := skb0
  let nestStart := skb
  let ret : Int := 0
  let mut done := true
  let mut peers : Option (Array PeerDumpAttrs) := some #[]
  let cursorDead : MixedM Bool := do
    let some pid := ctx.nextPeer | liftPrefix (invariant "unreachable")
    return (← getPeerMixed pid).isDead
  if ← orPrefix (rxBranch .dumpPeerListEmpty d.peerList.isEmpty)
      (andPrefix (rxBranch .dumpCursorSet ctx.nextPeer.isSome) (do rxBranch .dumpCursorDead (← cursorDead))) then
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
      _ ← rxBranch .dumpPeerIter true
      -- the handshake worker updates tx_bytes
      requireNotPendingMixed pid "dumping the peer"
      let (s, c, r) ← getPeerDumpPrefix pid ctx skb
      skb := s; ctx := c
      match r with
      | .complete peer =>
        _ ← rxBranch .dumpGetPeerFail false
        ps := ps.push peer
        nextCursor := some pid
      | .split peer =>
        _ ← rxBranch .dumpGetPeerFail true
        ps := ps.push peer
        done := false
        break
      | .cancelled =>
        _ ← rxBranch .dumpGetPeerFail true
        done := false
        break
    if done then _ ← rxBranch .dumpPeerIter false
    peers := some ps
  -- out: `!ret && !done && next_peer_cursor` takes the cursor's reference;
  -- the old cursor's is dropped
  if ← andPrefix (rxBranch .dumpOutRetZero (ret == 0))
      (andPrefix (rxBranch .dumpOutNotDone !done) (rxBranch .dumpOutHasCursor nextCursor.isSome)) then
    let some pid := nextCursor | liftPrefix (invariant "unreachable")
    peerGetMixed pid
  peerPutMixed ctx.nextPeer
  if ← rxBranch .dumpRetErr (ret != 0) then liftPrefix (unsupported "unreachable: the header and the nests fit")
  -- genlmsg_end: the data message is complete
  let message := NlMessage.data flags device (peers.map (·.toList))
  skb := { skb with messages := skb.messages ++ [message] }
  if ← rxBranch .dumpDone done then
    return { ret := 0, skb, ctx := { ctx with nextPeer := none }, prevSeq := seq }
  -- `return skb->len` (:296): the chunk's bytes so far, positive once the
  -- data message is in; `netlink_dump` reads its sign (audit F2)
  return { ret := Int.ofNat (NLMSG_GOODSIZE - skb.room), skb, ctx := { ctx with nextPeer := nextCursor }, prevSeq := seq }

def wgGetDeviceDumpPrefix (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) : MixedM DumpCall := do
  let d ← liftPrefix getDev
  let (s, flags, attrs) ← liftPrefix (deviceDumpHeaderSource d ctx prevSeq skb)
  deviceDumpTailPrefix d ctx s flags attrs

def netlinkDumpPrefix (fd : Nat) : MixedM Unit := do
  let mut sock ← liftPrefix (getNlSock fd)
  let mut skb : NlSkb := {}
  if sock.dumpDoneErrno > 0 then
    let r ← wgGetDeviceDumpPrefix sock.ctx sock.prevSeq skb
    -- `-EMSGSIZE` with data in the chunk (:2333-2334) is unreachable for
    -- WireGuard (2.3): the callback cancels its header before returning it
    skb := r.skb
    sock := { sock with ctx := r.ctx, prevSeq := r.prevSeq, dumpDoneErrno := r.ret }
  if sock.dumpDoneErrno > 0 || skb.room < nlmsgTotal 4 then
    liftPrefix (setNlSock fd { sock with queue := sock.queue ++ [skb] })
    return
  -- netlink_dump_done (:2225-2250): NLMSG_DONE carrying dump_done_errno,
  -- NLM_F_MULTI (the consistency flag never set here, 2.4)
  skb := { skb with room := skb.room - nlmsgTotal 4, messages := skb.messages ++ [.done 2 sock.dumpDoneErrno] }
  liftPrefix (setNlSock fd { sock with queue := sock.queue ++ [skb] })
  wgGetDeviceDonePrefix sock.ctx   -- cb->done (:2370)
  let after ← liftPrefix (getNlSock fd)
  liftPrefix (setNlSock fd { after with cbRunning := false })

def netlinkDumpStartPrefix (fd : Nat) (ref : DeviceRef) : MixedM Unit := do
  let sock ← liftPrefix (getNlSock fd)
  if sock.cbRunning then
    liftPrefix (unsupported "a dump start while the socket's dump runs (-EBUSY, af_netlink.c:2406): no WireGuard code runs")
  let wg ← liftPrefix (lookupInterface ref)
  if ← rxBranch .getStartErr (wg matches .error _) then
    let .error e := wg | liftPrefix (invariant "unreachable")
    -- `cb` is zeroed (:2417) before `start` (:2431), so the context and
    -- `prev_seq` are gone on a start error too (audit, the transport note)
    liftPrefix (setNlSock fd { sock with queue := sock.queue ++ [{ messages := [.error e] }], ctx := {}, prevSeq := 0 })
    return
  -- cb zeroed (:2422), then cb_running and dump_done_errno = INT_MAX (:2436-2437)
  liftPrefix (setNlSock fd { sock with cbRunning := true, dumpDoneErrno := INT_MAX, prevSeq := 0, ctx := { hasWg := true } })
  netlinkDumpPrefix fd

def netlinkRecvmsgPrefix (fd : Nat) : MixedM (Option (List NlMessage)) := do
  let sock ← liftPrefix (getNlSock fd)
  match sock.queue with
  | [] => return none
  | skb :: rest =>
    liftPrefix (setNlSock fd { sock with queue := rest })
    if (← liftPrefix (getNlSock fd)).cbRunning then netlinkDumpPrefix fd
    return some skb.messages

def wgGetDevicePrefix (ref : DeviceRef) : MixedM (Except Int Json) := do
  netlinkDumpStartPrefix 7 ref
  let mut messages : Array NlMessage := #[]
  let mut finished := false
  for _ in [0:4096] do
    if finished then break
    let some ms ← netlinkRecvmsgPrefix 7 | liftPrefix (invariant "op 9: nothing queued before the dump finished")
    for m in ms do
      messages := messages.push m
      match m with
      | .done .. | .error _ => finished := true
      | .data .. => pure ()
  if !finished then liftPrefix (invariant "op 9: the dump did not finish")
  liftPrefix (coalesce messages.toList)

theorem dumpUnsupported_sameKernel (s : String) : SameKernel (unsupported (α := α) s) := by
  intro w x v hr
  cases hr

theorem deviceDumpHeader_sameKernel (d : Device) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    SameKernel (deviceDumpHeaderSource d ctx prevSeq skb) := by
  unfold deviceDumpHeaderSource
  repeat' first
    | (dump_kernel_head Leanux.branch; with_reducible exact sameKernel_branch _ _)
    | (dump_kernel_head Leanux.unsupported; with_reducible exact dumpUnsupported_sameKernel _)
    | dump_kernel_step

theorem dumpMap_erases (f : α → β) {g : MixedM α} {a : M α}
    (he : ErasesPrefix g a) : ErasesPrefix (f <$> g) (f <$> a) := by
  simp only [map_eq_pure_bind]
  exact erasesPrefix_bind he (fun _ => erasesPrefix_pure _)

theorem dumpMap_preserves (c : AmbientContracts I) (f : α → β) {g : MixedM α}
    (hg : PrefixPreserves I LifetimeEvent.Safe g) : PrefixPreserves I LifetimeEvent.Safe (f <$> g) := by
  simp only [map_eq_pure_bind]
  exact hg.bind (fun _ => PrefixPreserves.pure c.safe _)

open Lean Meta Elab Tactic in
elab "dump_prefix_intro" : tactic => do
  unless (← getMainTarget).isForall do throwError "expected forall"
  evalTactic (← `(tactic| intro x))

theorem getPeerDumpPrefix_erases (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    ErasesPrefix (getPeerDumpPrefix pid ctx skb) (getPeerDump pid ctx skb) := by
  rw [getPeerDump_source]
  exact erasesPrefix_bind (getPeerMixed_erases pid) (fun _ => erasesPrefix_lift _)

theorem getPeerDumpPrefix_preserves (c : AmbientContracts I) (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    PrefixPreserves I LifetimeEvent.Safe (getPeerDumpPrefix pid ctx skb) :=
  PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
    (fun p => AmbientContracts.drop (c.kernel (fun _ => True) _ (getPeerDumpTail_sameKernel p ctx skb)))

theorem wgGetDeviceDonePrefix_erases (ctx : DumpCtx) :
    ErasesPrefix (wgGetDeviceDonePrefix ctx) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDonePrefix wgGetDeviceDone
  try simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact getPeerDumpPrefix_erases _ _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact requireNotPendingMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply dumpMap_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem wgGetDeviceDonePrefix_preserves (c : AmbientContracts I) (ctx : DumpCtx) :
    PrefixPreserves I LifetimeEvent.Safe (wgGetDeviceDonePrefix ctx) := by
  unfold wgGetDeviceDonePrefix
  repeat' first
    | with_reducible exact getPeerDumpPrefix_preserves c _ _ _
    | with_reducible exact AmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact getNlSock_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible exact coalesce_sameKernel _
    | with_reducible exact dumpUnsupported_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.range _ _ _ c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply dumpMap_preserves c
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem deviceDumpTailPrefix_erases (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Json)) :
    ErasesPrefix (deviceDumpTailPrefix d ctx skb flags attrs) (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailPrefix deviceDumpTailSource
  try simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact getPeerDumpPrefix_erases _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact requireNotPendingMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply dumpMap_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem deviceDumpTailPrefix_preserves (c : AmbientContracts I) (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Json)) :
    PrefixPreserves I LifetimeEvent.Safe (deviceDumpTailPrefix d ctx skb flags attrs) := by
  unfold deviceDumpTailPrefix
  repeat' first
    | with_reducible exact getPeerDumpPrefix_preserves c _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_preserves c _
    | with_reducible exact AmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact getNlSock_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible exact coalesce_sameKernel _
    | with_reducible exact dumpUnsupported_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.range _ _ _ c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply dumpMap_preserves c
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem wgGetDeviceDumpPrefix_erases (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    ErasesPrefix (wgGetDeviceDumpPrefix ctx prevSeq skb) (wgGetDeviceDump ctx prevSeq skb) := by
  rw [wgGetDeviceDump_source]
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun d =>
    erasesPrefix_bind (erasesPrefix_lift _) (fun s => deviceDumpTailPrefix_erases d ctx s.1 s.2.1 s.2.2))

theorem wgGetDeviceDumpPrefix_preserves (c : AmbientContracts I) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    PrefixPreserves I LifetimeEvent.Safe (wgGetDeviceDumpPrefix ctx prevSeq skb) :=
  PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)) (fun d =>
    PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (deviceDumpHeader_sameKernel d ctx prevSeq skb)))
      (fun s => deviceDumpTailPrefix_preserves c d ctx s.1 s.2.1 s.2.2))

theorem netlinkDumpPrefix_erases (fd : Nat) :
    ErasesPrefix (netlinkDumpPrefix fd) (netlinkDump fd) := by
  unfold netlinkDumpPrefix netlinkDump
  try simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact getPeerDumpPrefix_erases _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_erases _
    | with_reducible exact wgGetDeviceDumpPrefix_erases _ _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact requireNotPendingMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply dumpMap_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem netlinkDumpPrefix_preserves (c : AmbientContracts I) (stable : DumpStable I) (fd : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (netlinkDumpPrefix fd) := by
  unfold netlinkDumpPrefix
  repeat' first
    | with_reducible exact getPeerDumpPrefix_preserves c _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_preserves c _
    | with_reducible exact wgGetDeviceDumpPrefix_preserves c _ _ _
    | with_reducible exact dumpLift_preserves c stable _ (setNlSock_sameDumpKernel _ _)
    | with_reducible exact AmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact getNlSock_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible exact coalesce_sameKernel _
    | with_reducible exact dumpUnsupported_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.range _ _ _ c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply dumpMap_preserves c
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem netlinkDumpStartPrefix_erases (fd : Nat) (ref : DeviceRef) :
    ErasesPrefix (netlinkDumpStartPrefix fd ref) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStartPrefix netlinkDumpStart
  try simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact getPeerDumpPrefix_erases _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_erases _
    | with_reducible exact wgGetDeviceDumpPrefix_erases _ _ _
    | with_reducible exact netlinkDumpPrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact requireNotPendingMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply dumpMap_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem netlinkDumpStartPrefix_preserves (c : AmbientContracts I) (stable : DumpStable I) (fd : Nat) (ref : DeviceRef) :
    PrefixPreserves I LifetimeEvent.Safe (netlinkDumpStartPrefix fd ref) := by
  unfold netlinkDumpStartPrefix
  repeat' first
    | with_reducible exact getPeerDumpPrefix_preserves c _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_preserves c _
    | with_reducible exact wgGetDeviceDumpPrefix_preserves c _ _ _
    | with_reducible exact netlinkDumpPrefix_preserves c stable _
    | with_reducible exact dumpLift_preserves c stable _ (setNlSock_sameDumpKernel _ _)
    | with_reducible exact AmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact getNlSock_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible exact coalesce_sameKernel _
    | with_reducible exact dumpUnsupported_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.range _ _ _ c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply dumpMap_preserves c
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem netlinkRecvmsgPrefix_erases (fd : Nat) :
    ErasesPrefix (netlinkRecvmsgPrefix fd) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsgPrefix netlinkRecvmsg
  try simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact getPeerDumpPrefix_erases _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_erases _
    | with_reducible exact wgGetDeviceDumpPrefix_erases _ _ _
    | with_reducible exact netlinkDumpPrefix_erases _
    | with_reducible exact netlinkDumpStartPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact requireNotPendingMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply dumpMap_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem netlinkRecvmsgPrefix_preserves (c : AmbientContracts I) (stable : DumpStable I) (fd : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (netlinkRecvmsgPrefix fd) := by
  unfold netlinkRecvmsgPrefix
  repeat' first
    | with_reducible exact getPeerDumpPrefix_preserves c _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_preserves c _
    | with_reducible exact wgGetDeviceDumpPrefix_preserves c _ _ _
    | with_reducible exact netlinkDumpPrefix_preserves c stable _
    | with_reducible exact netlinkDumpStartPrefix_preserves c stable _ _
    | with_reducible exact dumpLift_preserves c stable _ (setNlSock_sameDumpKernel _ _)
    | with_reducible exact AmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact getNlSock_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible exact coalesce_sameKernel _
    | with_reducible exact dumpUnsupported_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.range _ _ _ c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply dumpMap_preserves c
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem wgGetDevicePrefix_erases (ref : DeviceRef) :
    ErasesPrefix (wgGetDevicePrefix ref) (wgGetDevice ref) := by
  unfold wgGetDevicePrefix wgGetDevice
  try simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact getPeerDumpPrefix_erases _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_erases _
    | with_reducible exact wgGetDeviceDumpPrefix_erases _ _ _
    | with_reducible exact netlinkDumpPrefix_erases _
    | with_reducible exact netlinkDumpStartPrefix_erases _ _
    | with_reducible exact netlinkRecvmsgPrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact requireNotPendingMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply dumpMap_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

theorem wgGetDevicePrefix_preserves (c : AmbientContracts I) (stable : DumpStable I) (ref : DeviceRef) :
    PrefixPreserves I LifetimeEvent.Safe (wgGetDevicePrefix ref) := by
  unfold wgGetDevicePrefix
  repeat' first
    | with_reducible exact getPeerDumpPrefix_preserves c _ _ _
    | with_reducible exact wgGetDeviceDonePrefix_preserves c _
    | with_reducible exact wgGetDeviceDumpPrefix_preserves c _ _ _
    | with_reducible exact netlinkDumpPrefix_preserves c stable _
    | with_reducible exact netlinkDumpStartPrefix_preserves c stable _ _
    | with_reducible exact netlinkRecvmsgPrefix_preserves c stable _
    | with_reducible exact dumpLift_preserves c stable _ (setNlSock_sameDumpKernel _ _)
    | with_reducible exact AmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply AmbientContracts.drop (c.kernel (fun _ => True) _ ?_)
    | with_reducible exact sameKernel_branch _ _
    | with_reducible exact getDev_sameKernel
    | with_reducible exact getNlSock_sameKernel _
    | with_reducible exact lookupInterface_sameKernel _
    | with_reducible exact coalesce_sameKernel _
    | with_reducible exact dumpUnsupported_sameKernel _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.range _ _ _ c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply dumpMap_preserves c
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (dump_prefix_intro; try dsimp only)
    | (with_reducible split)
    | simp_all
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _ | skip

/-- The seven original dump result types remain distinct. -/
inductive NetlinkDumpCall where
  | peer (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb)
  | chunk (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb)
  | done (ctx : DumpCtx)
  | dump (fd : Nat)
  | start (fd : Nat) (ref : DeviceRef)
  | receive (fd : Nat)
  | device (ref : DeviceRef)

namespace NetlinkDumpCall

def Result : NetlinkDumpCall → Type
  | .peer .. => NlSkb × DumpCtx × PeerDump
  | .chunk .. => DumpCall
  | .done .. | .dump .. | .start .. => Unit
  | .receive .. => Option (List NlMessage)
  | .device .. => Except Int Json

def original : (call : NetlinkDumpCall) → M call.Result
  | .peer p c s => getPeerDump p c s
  | .chunk c q s => wgGetDeviceDump c q s
  | .done c => wgGetDeviceDone c
  | .dump fd => netlinkDump fd
  | .start fd ref => netlinkDumpStart fd ref
  | .receive fd => netlinkRecvmsg fd
  | .device ref => wgGetDevice ref

def observed : (call : NetlinkDumpCall) → MixedM call.Result
  | .peer p c s => getPeerDumpPrefix p c s
  | .chunk c q s => wgGetDeviceDumpPrefix c q s
  | .done c => wgGetDeviceDonePrefix c
  | .dump fd => netlinkDumpPrefix fd
  | .start fd ref => netlinkDumpStartPrefix fd ref
  | .receive fd => netlinkRecvmsgPrefix fd
  | .device ref => wgGetDevicePrefix ref

theorem erases (call : NetlinkDumpCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | peer p c s => exact getPeerDumpPrefix_erases p c s
  | chunk c q s => exact wgGetDeviceDumpPrefix_erases c q s
  | done c => exact wgGetDeviceDonePrefix_erases c
  | dump fd => exact netlinkDumpPrefix_erases fd
  | start fd ref => exact netlinkDumpStartPrefix_erases fd ref
  | receive fd => exact netlinkRecvmsgPrefix_erases fd
  | device ref => exact wgGetDevicePrefix_erases ref

theorem preserves_ambient (c : AmbientContracts I) (stable : DumpStable I) (call : NetlinkDumpCall) :
    PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | peer p ctx s => exact getPeerDumpPrefix_preserves c p ctx s
  | chunk ctx q s => exact wgGetDeviceDumpPrefix_preserves c ctx q s
  | done ctx => exact wgGetDeviceDonePrefix_preserves c ctx
  | dump fd => exact netlinkDumpPrefix_preserves c stable fd
  | start fd ref => exact netlinkDumpStartPrefix_preserves c stable fd ref
  | receive fd => exact netlinkRecvmsgPrefix_preserves c stable fd
  | device ref => exact wgGetDevicePrefix_preserves c stable ref

theorem allocation (call : NetlinkDumpCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationDumpStable

end NetlinkDumpCall

end Leanux.Proofs.WG.Lifetimes
