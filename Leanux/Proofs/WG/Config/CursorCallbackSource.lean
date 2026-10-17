import Leanux.Proofs.WG.Config.SocketReadbackSource
import Leanux.Proofs.WG.Config.MultiPeerDumpSource
import Leanux.Proofs.WG.Config.FactoredTailClaims
import Leanux.Proofs.WG.Config.QueuedReferenceSource
import Leanux.Proofs.WG.Index.PeerRelease
import Leanux.Proofs.WG.Index.PeerReleaseOutcomeModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original ordered cursor acquisition, old-cursor release, and DATA return. -/
def cursorDumpFinish (d : Device) (flags : Nat) (device : List (String × Json))
    (ctx : DumpCtx) (nextCursor : Option PeerId) (skb : NlSkb) (done : Bool)
    (peers : Option (Array PeerDumpAttrs)) : WG.M DumpCall := do
  let ret : Int := 0
  if ← WG.andM (branch .dumpOutRetZero (ret == 0))
      (WG.andM (branch .dumpOutNotDone !done) (branch .dumpOutHasCursor nextCursor.isSome)) then
    let some pid := nextCursor | invariant "unreachable"
    peerGet pid
  peerPut ctx.nextPeer
  if ← branch .dumpRetErr (ret != 0) then unsupported "unreachable: the header and the nests fit"
  let message := NlMessage.data flags device (peers.map (·.toList))
  let skb := {skb with messages := skb.messages ++ [message]}
  if ← branch .dumpDone done then
    return {ret := 0,skb,ctx := {ctx with nextPeer := none},prevSeq := d.deviceUpdateGen}
  return {ret := Int.ofNat (NLMSG_GOODSIZE - skb.room), skb := skb, ctx := {ctx with nextPeer := nextCursor},prevSeq := d.deviceUpdateGen}

/-- The native finite loop and its actual end-of-iteration branch. -/
def cursorLoopFinish (d : Device) (ids : List PeerId) (ctx : DumpCtx) (flags : Nat)
    (device : List (String × Json)) (skb : NlSkb) : WG.M DumpCall := do
  let (outCtx,cursor,outSkb,done,attrs) ←
    forIn ids (ctx,ctx.nextPeer,skb,true,#[]) deviceDumpPeersStep
  if done then _ ← branch .dumpPeerIter false
  cursorDumpFinish d flags device outCtx cursor outSkb done (some attrs)

def cursorDumpGuard (d : Device) (ctx : DumpCtx) : WG.M Bool := do
  let cursorDead : WG.M Bool := do
    let some pid := ctx.nextPeer | invariant "unreachable"
    return (← getPeer pid).isDead
  WG.orM (branch .dumpPeerListEmpty d.peerList.isEmpty)
    (WG.andM (branch .dumpCursorSet ctx.nextPeer.isSome) (do branch .dumpCursorDead (← cursorDead)))

/-- Exact original guard and finite loop, with its reference-changing suffix opaque. -/
def cursorDumpBody (d : Device) (ctx : DumpCtx) (flags : Nat)
    (device : List (String × Json)) (skb0 : NlSkb) : WG.M DumpCall := do
  let (fail,skb) := skb0.put (nlaTotal 0)
  if ← branch .dumpNoPeersNest fail then unsupported "the peers nest does not fit a fresh chunk (unreachable)"
  if ← cursorDumpGuard d ctx then
    cursorDumpFinish d flags device ctx ctx.nextPeer skb true none
  else
    let ids : List PeerId := match ctx.nextPeer with
      | none => d.peerList
      | some pid => (d.peerList.dropWhile (· != pid)).drop 1
    cursorLoopFinish d ids ctx flags device skb

theorem socketDumpPeer_cursor_factor (d : Device) (ctx : DumpCtx) (flags : Nat)
    (device : List (String × Json)) (skb : NlSkb) :
    socketDumpPeerSource d ctx flags device skb = cursorDumpBody d ctx flags device skb := by
  simp only [socketDumpPeerSource,cursorDumpBody,cursorDumpGuard,cursorLoopFinish,cursorDumpFinish]
  rfl

theorem wgGetDeviceDump_cursor_factor (ctx : DumpCtx) (prev : Nat) (skb : NlSkb) :
    wgGetDeviceDump ctx prev skb = (do
      let d ← getDev
      socketDumpHeaderSource d ctx prev skb (cursorDumpBody d ctx)) := by
  rw [wgGetDeviceDump_source]
  simp only [socketDump_source]
  have body (d : Device) : socketDumpPeerSource d = cursorDumpBody d := by
    funext c f a s
    exact socketDumpPeer_cursor_factor d c f a s
  simp only [body]

end Leanux.Proofs.WG.Config
