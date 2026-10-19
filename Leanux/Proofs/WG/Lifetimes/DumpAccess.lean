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
open DumpComposition

def DumpStable (I : List LifetimeEvent → WGWorld → Prop) : Prop :=
  ∀ h w v, dumpView v = dumpView w → I h w → I h v

/-- The original product mask retains all 43 store fields except the two
dump sockets. Native leaves use the corresponding seven-field WG mask. -/
def productDumpView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter), dumpView w.wg)

def ProductDumpStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, productDumpView v = productDumpView w → I h w → I h v

theorem allocationDumpStable : DumpStable AllocationInv := by
  intro h w v he hi
  have hd := congrArg WGStoreView.dev he
  have hp := congrArg WGStoreView.peerCounter he
  have hk := congrArg WGStoreView.keypairCounter he
  have hn := congrArg WGStoreView.netIfindexNext he
  simp only [dumpView, dumpStore, wgStoreView] at hd hp hk hn
  apply hi.congr
  · unfold identityView
    congr 1
    · simp only [Peers.snapshot, hd, hp]
    · congr 1
      · funext id
        simp only [keypairResidents, hd]
      · funext slot
        simp only [packetResidents, hd]
  · simp only [allocationMetadata, hd, hk, hn]

theorem dumpLift_preserves (c : ProductAmbientContracts I) (stable : ProductDumpStable I)
    (a : Leanux.M α) (ha : SameView productDumpView a) :
    PrefixPreserves I LifetimeEvent.Safe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a c.safe
  intro h w x v hi hr
  exact stable h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

theorem dumpLift_preserves_native (c : AmbientContracts I) (stable : DumpStable I)
    (a : WG.M α) (ha : SameDump a) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift a (fun h w _ hi => c.safe h w hi)
  intro h w ambient x v ambient' hi hr
  exact stable h w v ((ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr) hi

theorem dumpLift_native_product (c : ProductAmbientContracts I) (stable : ProductDumpStable I)
    (a : WG.M α) (ha : SameDump a) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) := by
  rw [liftWGObserver_lift]
  apply dumpLift_preserves c stable (liftWG a)
  apply sameView_liftWG productDumpView dumpView a ha
  intro w g ambient hg
  change (_, _, _, dumpView g) = (_, _, _, dumpView w.wg)
  rw [hg]

def getPeerDumpPrefix (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    MixedM (NlSkb × DumpCtx × PeerDump) := do
  let p ← getPeerMixed pid
  liftWGPrefix (getPeerDumpTailSource p ctx skb)

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
  let (fail, s) := skb.put (nlaTotal 0); skb := s
  if ← rxBranch .dumpNoPeersNest fail then
    liftWGPrefix (unsupported "the peers nest does not fit a fresh chunk (unreachable)")
  let ret : Int := 0
  let mut done := true
  let mut peers : Option (Array PeerDumpAttrs) := some #[]
  let cursorDead : MixedM Bool := do
    let some pid := ctx.nextPeer | liftWGPrefix (invariant "unreachable")
    return (← getPeerMixed pid).isDead
  if ← orPrefix (rxBranch .dumpPeerListEmpty d.peerList.isEmpty)
      (andPrefix (rxBranch .dumpCursorSet ctx.nextPeer.isSome) (do rxBranch .dumpCursorDead (← cursorDead))) then
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
    let some pid := nextCursor | liftWGPrefix (invariant "unreachable")
    peerGetMixed pid
  peerPutMixed ctx.nextPeer
  if ← rxBranch .dumpRetErr (ret != 0) then liftWGPrefix (unsupported "unreachable: the header and the nests fit")
  -- genlmsg_end: the data message is complete
  let message := NlMessage.data flags device (peers.map (·.toList))
  skb := { skb with messages := skb.messages ++ [message] }
  if ← rxBranch .dumpDone done then
    return { ret := 0, skb, ctx := { ctx with nextPeer := none }, prevSeq := seq }
  -- `return skb->len` (:296): the chunk's bytes so far, positive once the
  -- data message is in; `netlink_dump` reads its sign (audit F2)
  return { ret := Int.ofNat (NLMSG_GOODSIZE - skb.room), skb, ctx := { ctx with nextPeer := nextCursor }, prevSeq := seq }

def wgGetDeviceDumpPrefix (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) : MixedM DumpCall := do
  let d ← liftWGPrefix getDev
  let (s, flags, attrs) ← liftWGPrefix (deviceDumpHeaderSource d ctx prevSeq skb)
  deviceDumpTailPrefix d ctx s flags attrs

def netlinkDumpPrefix (fd : Nat) : MixedM Unit := do
  let mut sock ← liftWGPrefix (getNlSock fd)
  let mut skb : NlSkb := {}
  if sock.dumpDoneErrno > 0 then
    let r ← wgGetDeviceDumpPrefix sock.ctx sock.prevSeq skb
    -- `-EMSGSIZE` with data in the chunk (:2333-2334) is unreachable for
    -- WireGuard (2.3): the callback cancels its header before returning it
    skb := r.skb
    sock := { sock with ctx := r.ctx, prevSeq := r.prevSeq, dumpDoneErrno := r.ret }
  if sock.dumpDoneErrno > 0 || skb.room < nlmsgTotal 4 then
    liftWGPrefix (setNlSock fd { sock with queue := sock.queue ++ [skb] })
    return
  -- netlink_dump_done (:2225-2250): NLMSG_DONE carrying dump_done_errno,
  -- NLM_F_MULTI (the consistency flag never set here, 2.4)
  skb := { skb with room := skb.room - nlmsgTotal 4, messages := skb.messages ++ [.done 2 sock.dumpDoneErrno] }
  liftWGPrefix (setNlSock fd { sock with queue := sock.queue ++ [skb] })
  wgGetDeviceDonePrefix sock.ctx   -- cb->done (:2370)
  let after ← liftWGPrefix (getNlSock fd)
  liftWGPrefix (setNlSock fd { after with cbRunning := false })

def netlinkDumpStartPrefix (fd : Nat) (ref : DeviceRef) : MixedM Unit := do
  let sock ← liftWGPrefix (getNlSock fd)
  if sock.cbRunning then
    liftWGPrefix (unsupported "a dump start while the socket's dump runs (-EBUSY, af_netlink.c:2406): no WireGuard code runs")
  let wg ← liftWGPrefix (lookupInterface ref)
  if ← rxBranch .getStartErr (wg matches .error _) then
    let .error e := wg | liftWGPrefix (invariant "unreachable")
    -- `cb` is zeroed (:2417) before `start` (:2431), so the context and
    -- `prev_seq` are gone on a start error too (audit, the transport note)
    liftWGPrefix (setNlSock fd { sock with queue := sock.queue ++ [{ messages := [.error e] }], ctx := {}, prevSeq := 0 })
    return
  -- cb zeroed (:2422), then cb_running and dump_done_errno = INT_MAX (:2436-2437)
  liftWGPrefix (setNlSock fd { sock with cbRunning := true, dumpDoneErrno := INT_MAX, prevSeq := 0, ctx := { hasWg := true } })
  netlinkDumpPrefix fd

def netlinkRecvmsgPrefix (fd : Nat) : MixedM (Option (List NlMessage)) := do
  let sock ← liftWGPrefix (getNlSock fd)
  match sock.queue with
  | [] => return none
  | skb :: rest =>
    liftWGPrefix (setNlSock fd { sock with queue := rest })
    if (← liftWGPrefix (getNlSock fd)).cbRunning then netlinkDumpPrefix fd
    return some skb.messages

def wgGetDevicePrefix (ref : DeviceRef) : MixedM (Except Int Json) := do
  netlinkDumpStartPrefix 7 ref
  let mut messages : Array NlMessage := #[]
  let mut finished := false
  for _ in [0:4096] do
    if finished then break
    let some ms ← netlinkRecvmsgPrefix 7 | liftWGPrefix (invariant "op 9: nothing queued before the dump finished")
    for m in ms do
      messages := messages.push m
      match m with
      | .done .. | .error _ => finished := true
      | .data .. => pure ()
  if !finished then liftWGPrefix (invariant "op 9: the dump did not finish")
  liftWGPrefix (coalesce messages.toList)

theorem deviceDumpHeader_sameWGStore (d : Device) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    SameWGStore (deviceDumpHeaderSource d ctx prevSeq skb) := by
  change SameView wgStoreView _
  unfold deviceDumpHeaderSource
  repeat' first
    | (dump_kernel_head Leanux.branch; exact fun initial =>
        hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))
    | (dump_kernel_head Leanux.unsupported; exact fun initial =>
        hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))
    | dump_kernel_step

theorem dumpMap_erases (f : α → β) {g : PrefixM LifetimeEvent α} {a : Leanux.M α}
    (he : ErasesPrefix g a) : ErasesPrefix (f <$> g) (f <$> a) := by
  simp only [map_eq_pure_bind]
  exact erasesPrefix_bind he (fun _ => erasesPrefix_pure _)

theorem dumpMap_preserves (c : ProductAmbientContracts I) (f : α → β)
    {g : PrefixM LifetimeEvent α} (hg : PrefixPreserves I LifetimeEvent.Safe g) :
    PrefixPreserves I LifetimeEvent.Safe (f <$> g) := by
  simp only [map_eq_pure_bind]
  exact hg.bind (fun _ => PrefixPreserves.pure c.safe _)

theorem dumpMap_erases_native (f : α → β) {g : MixedM α} {a : WG.M α}
    (he : ErasesStatePrefix g a) : ErasesStatePrefix (f <$> g) (f <$> a) := by
  simp only [map_eq_pure_bind]
  exact erasesStatePrefix_bind he (fun _ => erasesStatePrefix_pure _)

theorem dumpMap_preserves_native (c : AmbientContracts I) (f : α → β) {g : MixedM α}
    (hg : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe g) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (f <$> g) := by
  simp only [map_eq_pure_bind]
  exact StatePrefixEnsures.bind hg (fun _ =>
    StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))


theorem getPeerDumpPrefix_erases (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    ErasesStatePrefix (getPeerDumpPrefix pid ctx skb) (getPeerDump pid ctx skb) := by
  rw [getPeerDump_source]
  exact erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ => erasesStatePrefix_lift _)

theorem wgGetDeviceDonePrefix_erases (ctx : DumpCtx) :
    ErasesStatePrefix (wgGetDeviceDonePrefix ctx) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDonePrefix wgGetDeviceDone
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_erases _ _ _ )
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head peerGetMixed; exact peerGetMixed_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head requireNotPendingMixed; exact requireNotPendingMixed_erases _ _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head Functor.map; apply dumpMap_erases_native)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem deviceDumpTailPrefix_erases (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Json)) :
    ErasesStatePrefix (deviceDumpTailPrefix d ctx skb flags attrs) (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailPrefix deviceDumpTailSource
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_erases _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_erases _ )
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head peerGetMixed; exact peerGetMixed_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head requireNotPendingMixed; exact requireNotPendingMixed_erases _ _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head Functor.map; apply dumpMap_erases_native)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem wgGetDeviceDumpPrefix_erases (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    ErasesStatePrefix (wgGetDeviceDumpPrefix ctx prevSeq skb) (wgGetDeviceDump ctx prevSeq skb) := by
  rw [wgGetDeviceDump_source]
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun d =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun s => deviceDumpTailPrefix_erases d ctx s.1 s.2.1 s.2.2))

theorem netlinkDumpPrefix_erases (fd : Nat) :
    ErasesStatePrefix (netlinkDumpPrefix fd) (netlinkDump fd) := by
  unfold netlinkDumpPrefix netlinkDump
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_erases _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_erases _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_erases _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_erases _ _ _ )
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head peerGetMixed; exact peerGetMixed_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head requireNotPendingMixed; exact requireNotPendingMixed_erases _ _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head Functor.map; apply dumpMap_erases_native)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem netlinkDumpStartPrefix_erases (fd : Nat) (ref : DeviceRef) :
    ErasesStatePrefix (netlinkDumpStartPrefix fd ref) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStartPrefix netlinkDumpStart
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_erases _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_erases _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_erases _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_erases _ _ _ )
    | (maintenance_head netlinkDumpPrefix; exact netlinkDumpPrefix_erases _ )
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head peerGetMixed; exact peerGetMixed_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head requireNotPendingMixed; exact requireNotPendingMixed_erases _ _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head Functor.map; apply dumpMap_erases_native)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem netlinkRecvmsgPrefix_erases (fd : Nat) :
    ErasesStatePrefix (netlinkRecvmsgPrefix fd) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsgPrefix netlinkRecvmsg
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_erases _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_erases _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_erases _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_erases _ _ _ )
    | (maintenance_head netlinkDumpPrefix; exact netlinkDumpPrefix_erases _ )
    | (maintenance_head netlinkDumpStartPrefix; exact netlinkDumpStartPrefix_erases _ _ )
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head peerGetMixed; exact peerGetMixed_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head requireNotPendingMixed; exact requireNotPendingMixed_erases _ _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head Functor.map; apply dumpMap_erases_native)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem wgGetDevicePrefix_erases (ref : DeviceRef) :
    ErasesStatePrefix (wgGetDevicePrefix ref) (wgGetDevice ref) := by
  unfold wgGetDevicePrefix wgGetDevice
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_erases _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_erases _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_erases _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_erases _ _ _ )
    | (maintenance_head netlinkDumpPrefix; exact netlinkDumpPrefix_erases _ )
    | (maintenance_head netlinkDumpStartPrefix; exact netlinkDumpStartPrefix_erases _ _ )
    | (maintenance_head netlinkRecvmsgPrefix; exact netlinkRecvmsgPrefix_erases _ )
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head peerGetMixed; exact peerGetMixed_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head requireNotPendingMixed; exact requireNotPendingMixed_erases _ _)
    | (maintenance_head andPrefix; unfold andPrefix WG.andM)
    | (maintenance_head orPrefix; unfold orPrefix WG.orM)
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | (maintenance_head Functor.map; apply dumpMap_erases_native)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem getPeerDumpPrefix_preserves (c : AmbientContracts I) (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (getPeerDumpPrefix pid ctx skb) := by
  change StatePrefixEnsures _ _ _ _
  unfold getPeerDumpPrefix
  repeat' first
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact AmbientContracts.drop (c.store (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact AmbientContracts.drop (c.store (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head Functor.map; apply dumpMap_preserves_native c)
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgGetDeviceDonePrefix_preserves (c : AmbientContracts I) (ctx : DumpCtx) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (wgGetDeviceDonePrefix ctx) := by
  change StatePrefixEnsures _ _ _ _
  unfold wgGetDeviceDonePrefix
  repeat' first
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves c _ _ _ )
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact AmbientContracts.drop (c.store (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact AmbientContracts.drop (c.store (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head Functor.map; apply dumpMap_preserves_native c)
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem deviceDumpTailPrefix_preserves (c : AmbientContracts I) (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Json)) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (deviceDumpTailPrefix d ctx skb flags attrs) := by
  change StatePrefixEnsures _ _ _ _
  unfold deviceDumpTailPrefix
  repeat' first
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves c _ )
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact AmbientContracts.drop (c.store (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact AmbientContracts.drop (c.store (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head Functor.map; apply dumpMap_preserves_native c)
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgGetDeviceDumpPrefix_preserves (c : AmbientContracts I) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (wgGetDeviceDumpPrefix ctx prevSeq skb) := by
  change StatePrefixEnsures _ _ _ _
  unfold wgGetDeviceDumpPrefix
  repeat' first
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves c _ _ _ _ _ )
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact AmbientContracts.drop (c.store (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact AmbientContracts.drop (c.store (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head Functor.map; apply dumpMap_preserves_native c)
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem netlinkDumpPrefix_preserves (c : AmbientContracts I) (stable : DumpStable I) (fd : Nat) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (netlinkDumpPrefix fd) := by
  change StatePrefixEnsures _ _ _ _
  unfold netlinkDumpPrefix
  repeat' first
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves c _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_preserves c _ _ _ )
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact AmbientContracts.drop (c.store (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact AmbientContracts.drop (c.store (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head setNlSock; exact dumpLift_preserves_native c stable _ (setNlSock_sameDump _ _))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head Functor.map; apply dumpMap_preserves_native c)
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem netlinkDumpStartPrefix_preserves (c : AmbientContracts I) (stable : DumpStable I) (fd : Nat) (ref : DeviceRef) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (netlinkDumpStartPrefix fd ref) := by
  change StatePrefixEnsures _ _ _ _
  unfold netlinkDumpStartPrefix
  repeat' first
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves c _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_preserves c _ _ _ )
    | (maintenance_head netlinkDumpPrefix; exact netlinkDumpPrefix_preserves c stable _ )
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact AmbientContracts.drop (c.store (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact AmbientContracts.drop (c.store (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head setNlSock; exact dumpLift_preserves_native c stable _ (setNlSock_sameDump _ _))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head Functor.map; apply dumpMap_preserves_native c)
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem netlinkRecvmsgPrefix_preserves (c : AmbientContracts I) (stable : DumpStable I) (fd : Nat) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (netlinkRecvmsgPrefix fd) := by
  change StatePrefixEnsures _ _ _ _
  unfold netlinkRecvmsgPrefix
  repeat' first
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves c _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_preserves c _ _ _ )
    | (maintenance_head netlinkDumpPrefix; exact netlinkDumpPrefix_preserves c stable _ )
    | (maintenance_head netlinkDumpStartPrefix; exact netlinkDumpStartPrefix_preserves c stable _ _ )
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact AmbientContracts.drop (c.store (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact AmbientContracts.drop (c.store (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head setNlSock; exact dumpLift_preserves_native c stable _ (setNlSock_sameDump _ _))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head Functor.map; apply dumpMap_preserves_native c)
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgGetDevicePrefix_preserves (c : AmbientContracts I) (stable : DumpStable I) (ref : DeviceRef) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (wgGetDevicePrefix ref) := by
  change StatePrefixEnsures _ _ _ _
  unfold wgGetDevicePrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves c _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_preserves c _ _ _ )
    | (maintenance_head netlinkDumpPrefix; exact netlinkDumpPrefix_preserves c stable _ )
    | (maintenance_head netlinkDumpStartPrefix; exact netlinkDumpStartPrefix_preserves c stable _ _ )
    | (maintenance_head netlinkRecvmsgPrefix; exact netlinkRecvmsgPrefix_preserves c stable _ )
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact AmbientContracts.drop (c.store (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact AmbientContracts.drop (c.store (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact AmbientContracts.drop (c.store (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact AmbientContracts.drop (c.store (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head setNlSock; exact dumpLift_preserves_native c stable _ (setNlSock_sameDump _ _))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi); intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | (maintenance_head Functor.map; apply dumpMap_preserves_native c)
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem getPeerDumpPrefix_preserves_product (c : ProductAmbientContracts I) (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (getPeerDumpPrefix pid ctx skb)) := by
  change PrefixEnsures _ _ _ _
  unfold getPeerDumpPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | (maintenance_head Functor.map; simp only [map_eq_pure_bind])
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgGetDeviceDonePrefix_preserves_product (c : ProductAmbientContracts I) (ctx : DumpCtx) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (wgGetDeviceDonePrefix ctx)) := by
  change PrefixEnsures _ _ _ _
  unfold wgGetDeviceDonePrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | (maintenance_head Functor.map; simp only [map_eq_pure_bind])
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem deviceDumpTailPrefix_preserves_product (c : ProductAmbientContracts I) (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Json)) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (deviceDumpTailPrefix d ctx skb flags attrs)) := by
  change PrefixEnsures _ _ _ _
  unfold deviceDumpTailPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves_product c _ )
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | (maintenance_head Functor.map; simp only [map_eq_pure_bind])
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgGetDeviceDumpPrefix_preserves_product (c : ProductAmbientContracts I) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (wgGetDeviceDumpPrefix ctx prevSeq skb)) := by
  change PrefixEnsures _ _ _ _
  unfold wgGetDeviceDumpPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves_product c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves_product c _ _ _ _ _ )
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | (maintenance_head Functor.map; simp only [map_eq_pure_bind])
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem netlinkDumpPrefix_preserves_product (c : ProductAmbientContracts I) (stable : ProductDumpStable I) (fd : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (netlinkDumpPrefix fd)) := by
  change PrefixEnsures _ _ _ _
  unfold netlinkDumpPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves_product c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves_product c _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head setNlSock; exact dumpLift_native_product c stable _ (setNlSock_sameDump _ _))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | (maintenance_head Functor.map; simp only [map_eq_pure_bind])
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem netlinkDumpStartPrefix_preserves_product (c : ProductAmbientContracts I) (stable : ProductDumpStable I) (fd : Nat) (ref : DeviceRef) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (netlinkDumpStartPrefix fd ref)) := by
  change PrefixEnsures _ _ _ _
  unfold netlinkDumpStartPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves_product c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves_product c _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head netlinkDumpPrefix; exact netlinkDumpPrefix_preserves_product c stable _ )
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head setNlSock; exact dumpLift_native_product c stable _ (setNlSock_sameDump _ _))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | (maintenance_head Functor.map; simp only [map_eq_pure_bind])
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem netlinkRecvmsgPrefix_preserves_product (c : ProductAmbientContracts I) (stable : ProductDumpStable I) (fd : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (netlinkRecvmsgPrefix fd)) := by
  change PrefixEnsures _ _ _ _
  unfold netlinkRecvmsgPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves_product c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves_product c _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head netlinkDumpPrefix; exact netlinkDumpPrefix_preserves_product c stable _ )
    | (maintenance_head netlinkDumpStartPrefix; exact netlinkDumpStartPrefix_preserves_product c stable _ _ )
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head setNlSock; exact dumpLift_native_product c stable _ (setNlSock_sameDump _ _))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | (maintenance_head Functor.map; simp only [map_eq_pure_bind])
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgGetDevicePrefix_preserves_product (c : ProductAmbientContracts I) (stable : ProductDumpStable I) (ref : DeviceRef) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (wgGetDevicePrefix ref)) := by
  change PrefixEnsures _ _ _ _
  unfold wgGetDevicePrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [liftWGObserver_forIn] | rw [apply_ite])
    | (maintenance_head getPeerDumpPrefix; exact getPeerDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head wgGetDeviceDonePrefix; exact wgGetDeviceDonePrefix_preserves_product c _ )
    | (maintenance_head deviceDumpTailPrefix; exact deviceDumpTailPrefix_preserves_product c _ _ _ _ _ )
    | (maintenance_head wgGetDeviceDumpPrefix; exact wgGetDeviceDumpPrefix_preserves_product c _ _ _ )
    | (maintenance_head netlinkDumpPrefix; exact netlinkDumpPrefix_preserves_product c stable _ )
    | (maintenance_head netlinkDumpStartPrefix; exact netlinkDumpStartPrefix_preserves_product c stable _ _ )
    | (maintenance_head netlinkRecvmsgPrefix; exact netlinkRecvmsgPrefix_preserves_product c stable _ )
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head requireNotPendingMixed; exact ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) _ _))
    | (maintenance_head rxBranch; unfold rxBranch)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head deviceDumpHeaderSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (deviceDumpHeader_sameWGStore _ _ _ _)))
    | (maintenance_lift_action_head getPeerDumpTailSource; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getPeerDumpTail_sameWGWorld _ _ _).factor wgStoreView)))
    | (maintenance_lift_action_head getNlSock; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((getNlSock_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head lookupInterface; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((lookupInterface_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head coalesce; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((coalesce_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.unsupported _) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head setNlSock; exact dumpLift_native_product c stable _ (setNlSock_sameDump _ _))
    | (maintenance_head andPrefix; unfold andPrefix)
    | (maintenance_head orPrefix; unfold orPrefix)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | (maintenance_head Functor.map; simp only [map_eq_pure_bind])
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

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

def original : (call : NetlinkDumpCall) → WG.M call.Result
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

theorem erases (call : NetlinkDumpCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | peer p c s => exact getPeerDumpPrefix_erases p c s
  | chunk c q s => exact wgGetDeviceDumpPrefix_erases c q s
  | done c => exact wgGetDeviceDonePrefix_erases c
  | dump fd => exact netlinkDumpPrefix_erases fd
  | start fd ref => exact netlinkDumpStartPrefix_erases fd ref
  | receive fd => exact netlinkRecvmsgPrefix_erases fd
  | device ref => exact wgGetDevicePrefix_erases ref

theorem preserves_ambient (c : AmbientContracts I) (stable : DumpStable I) (call : NetlinkDumpCall) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | peer p ctx s => exact getPeerDumpPrefix_preserves c p ctx s
  | chunk ctx q s => exact wgGetDeviceDumpPrefix_preserves c ctx q s
  | done ctx => exact wgGetDeviceDonePrefix_preserves c ctx
  | dump fd => exact netlinkDumpPrefix_preserves c stable fd
  | start fd ref => exact netlinkDumpStartPrefix_preserves c stable fd ref
  | receive fd => exact netlinkRecvmsgPrefix_preserves c stable fd
  | device ref => exact wgGetDevicePrefix_preserves c stable ref

theorem preserves_ambient_product (c : ProductAmbientContracts I) (stable : ProductDumpStable I) (call : NetlinkDumpCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | peer p ctx s => exact getPeerDumpPrefix_preserves_product c p ctx s
  | chunk ctx q s => exact wgGetDeviceDumpPrefix_preserves_product c ctx q s
  | done ctx => exact wgGetDeviceDonePrefix_preserves_product c ctx
  | dump fd => exact netlinkDumpPrefix_preserves_product c stable fd
  | start fd ref => exact netlinkDumpStartPrefix_preserves_product c stable fd ref
  | receive fd => exact netlinkRecvmsgPrefix_preserves_product c stable fd
  | device ref => exact wgGetDevicePrefix_preserves_product c stable ref

theorem allocation (call : NetlinkDumpCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationDumpStable

end NetlinkDumpCall

end Leanux.Proofs.WG.Lifetimes
