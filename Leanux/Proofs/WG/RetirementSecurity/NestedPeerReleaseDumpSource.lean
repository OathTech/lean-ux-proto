import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseSource
import Leanux.Proofs.WG.Queues.DumpReservation

/-! Native dump cursor repayment through exact existing header/walk factors.
A dead old cursor can be the final reference; its release is not assumed quiet. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged
open NetlinkDump Queues.RxCredits

variable {m : Type → Type} [Monad m]

def dumpDoneWith (o : Ops m) (ctx : DumpCtx) : m Unit := do
  _ ← o.step (branch .getDoneHasWg ctx.hasWg)
  o.release ctx.nextPeer

def dumpReplaceWith (o : Ops m) (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) : m Unit := do
  if ← o.step (WG.andM (branch .dumpOutRetZero ((0 : Int) == 0))
      (WG.andM (branch .dumpOutNotDone !done) (branch .dumpOutHasCursor nextCursor.isSome))) then
    let some pid := nextCursor | o.step (invariant "unreachable")
    o.step (peerGet pid)
  o.release ctx.nextPeer

def dumpFinishWith (o : Ops m) (seq : UInt32) (ctx : DumpCtx) (nextCursor : Option PeerId)
    (skb0 : NlSkb) (flags : Nat) (device : List (String × Lean.Json)) (done : Bool)
    (peers : Option (Array PeerDumpAttrs)) : m DumpCall := do
  dumpReplaceWith o ctx nextCursor done
  if ← o.step (branch .dumpRetErr ((0 : Int) != 0)) then
    o.step (unsupported "unreachable: the header and the nests fit")
  let message := NlMessage.data flags device (peers.map (·.toList))
  let skb := { skb0 with messages := skb0.messages ++ [message] }
  if ← o.step (branch .dumpDone done) then
    return { ret := 0, skb, ctx := { ctx with nextPeer := none }, prevSeq := seq }
  return { ret := Int.ofNat (NLMSG_GOODSIZE - skb.room), skb, ctx := { ctx with nextPeer := nextCursor }, prevSeq := seq }

def dumpTailWith (o : Ops m) (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) : m DumpCall := do
  let (ctx,nextCursor,skb,done,peers) ← o.step (DumpReservation.walkSource d ctx skb)
  dumpFinishWith o d.deviceUpdateGen ctx nextCursor skb flags attrs done peers

def dumpChunkWith (o : Ops m) (ctx : DumpCtx) (prevSeq : UInt32) (skb : NlSkb) : m DumpCall := do
  let d ← o.step getDev
  let (s,flags,attrs) ← o.step (deviceDumpHeaderSource d ctx prevSeq skb)
  dumpTailWith o d ctx s flags attrs

def dumpSocketWith (o : Ops m) (fd : Nat) : m Unit := do
  let mut sock ← o.step (getNlSock fd)
  let mut skb : NlSkb := {}
  if sock.dumpDoneErrno > 0 then
    let r ← dumpChunkWith o sock.ctx sock.prevSeq skb
    skb := r.skb
    sock := { sock with ctx := r.ctx, prevSeq := r.prevSeq, dumpDoneErrno := r.ret }
  if sock.dumpDoneErrno > 0 || skb.room < nlmsgTotal 4 then
    o.step (setNlSock fd { sock with queue := sock.queue ++ [skb] })
    return
  skb := { skb with room := skb.room - nlmsgTotal 4, messages := skb.messages ++ [.done 2 sock.dumpDoneErrno] }
  o.step (setNlSock fd { sock with queue := sock.queue ++ [skb] })
  dumpDoneWith o sock.ctx
  let after ← o.step (getNlSock fd)
  o.step (setNlSock fd { after with cbRunning := false })

def dumpStartWith (o : Ops m) (fd : Nat) (ref : DeviceRef) : m Unit := do
  let sock ← o.step (getNlSock fd)
  if sock.cbRunning then
    o.step (unsupported "a dump start while the socket's dump runs (-EBUSY, af_netlink.c:2406): no WireGuard code runs")
  let wg ← o.step (lookupInterface ref)
  if ← o.step (branch .getStartErr (wg matches .error _)) then
    let .error e := wg | o.step (invariant "unreachable")
    o.step (setNlSock fd { sock with queue := sock.queue ++ [{ messages := [.error e] }], ctx := {}, prevSeq := 0 })
    return
  o.step (setNlSock fd { sock with cbRunning := true, dumpDoneErrno := INT_MAX, prevSeq := 0, ctx := { hasWg := true } })
  dumpSocketWith o fd

def dumpReceiveWith (o : Ops m) (fd : Nat) : m (Option (List NlMessage)) := do
  let sock ← o.step (getNlSock fd)
  match sock.queue with
  | [] => return none
  | skb :: rest =>
    o.step (setNlSock fd { sock with queue := rest })
    if (← o.step (getNlSock fd)).cbRunning then dumpSocketWith o fd
    return some skb.messages

def dumpDeviceWith (o : Ops m) (ref : DeviceRef) : m (Except Int Lean.Json) := do
  dumpStartWith o 7 ref
  let mut messages : Array NlMessage := #[]
  let mut finished := false
  for _ in [0:4096] do
    if finished then break
    let some ms ← dumpReceiveWith o 7 | o.step (invariant "op 9: nothing queued before the dump finished")
    for msg in ms do
      messages := messages.push msg
      match msg with
      | .done .. | .error _ => finished := true
      | .data .. => pure ()
  if !finished then o.step (invariant "op 9: the dump did not finish")
  o.step (coalesce messages.toList)

theorem dumpDone_native (ctx : DumpCtx) : dumpDoneWith native ctx = wgGetDeviceDone ctx := rfl

theorem dumpReplace_native (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) :
    dumpReplaceWith native ctx nextCursor done = DumpReservation.replaceSource ctx nextCursor done := rfl

theorem dumpFinish_native (seq : UInt32) (ctx : DumpCtx) (nextCursor : Option PeerId)
    (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) (done : Bool)
    (peers : Option (Array PeerDumpAttrs)) :
    dumpFinishWith native seq ctx nextCursor skb flags attrs done peers =
      DumpReservation.finishSource seq ctx nextCursor skb flags attrs done peers := rfl

theorem dumpTail_native (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    dumpTailWith native d ctx skb flags attrs = deviceDumpTailSource d ctx skb flags attrs := by
  rw [DumpReservation.tail_factor]
  rfl

theorem dumpChunk_native (ctx : DumpCtx) (prevSeq : UInt32) (skb : NlSkb) :
    dumpChunkWith native ctx prevSeq skb = wgGetDeviceDump ctx prevSeq skb := by
  rw [wgGetDeviceDump_source]
  unfold dumpChunkWith
  simp only [dumpTail_native]
  rfl

theorem dumpSocket_native (fd : Nat) : dumpSocketWith native fd = netlinkDump fd := by
  unfold dumpSocketWith netlinkDump
  simp only [dumpChunk_native,dumpDone_native]
  rfl

theorem dumpStart_native (fd : Nat) (ref : DeviceRef) :
    dumpStartWith native fd ref = netlinkDumpStart fd ref := by
  unfold dumpStartWith netlinkDumpStart
  simp only [dumpSocket_native]
  rfl

theorem dumpReceive_native (fd : Nat) : dumpReceiveWith native fd = netlinkRecvmsg fd := by
  unfold dumpReceiveWith netlinkRecvmsg
  simp only [dumpSocket_native]
  rfl

theorem dumpDevice_native (ref : DeviceRef) : dumpDeviceWith native ref = wgGetDevice ref := by
  unfold dumpDeviceWith wgGetDevice
  simp only [dumpStart_native,dumpReceive_native]
  rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
