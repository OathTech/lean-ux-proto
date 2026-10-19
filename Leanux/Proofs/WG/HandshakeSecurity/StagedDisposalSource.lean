import Leanux.Proofs.WG.Lifetimes.DeviceXmit
import Leanux.Proofs.Logged.NativeCapture
import Leanux.Proofs.WG.Peers.Access

/-! Native staged disposal boundaries. The final peer release is split after
the counted queue purge, before the timer invariant and dispatch retirement.
This permits a receipt to survive a Stop in that later suffix. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged

def releaseFinish (pid : PeerId) (p : Peer) : WG.M Unit := do
  if let some t := PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome) then
    invariant s!"peer {pid} released with its {repr t} timer pending"
  retirePeerUnits pid

/-- Execute the original reference decrement and, only on its final-release
arm, the actual counted erase. The returned peer is the original native read. -/
def releaseCut (peer : Option PeerId) : WG.M (Option (PeerId × Peer)) := do
  if ← branch .peerPutNull peer.isNone then return none
  let some pid := peer | invariant "unreachable"
  requireNotPending pid "a reference count the handshake worker also changes"
  let p ← getPeer pid
  setPeer pid {p with refcount := p.refcount - 1}
  if ← branch .peerKrefPutReleased (← refcountDecAndTest p.refcount) then
    indexRemove (.handshake pid)
    if p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty then
      invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)"
    modifyDev fun d => {d with txDropped := d.txDropped + p.staged.length, peers := d.peers.erase pid}
    return some (pid,p)
  return none

theorem release_factor (peer : Option PeerId) : peerPut peer = (do
    match ← releaseCut peer with
    | none => pure ()
    | some (pid,p) => releaseFinish pid p) := by
  unfold peerPut releaseCut releaseFinish
  simp only [bind_assoc]
  congr 1
  funext empty
  split
  · rfl
  · cases peer with
    | none => rfl
    | some pid =>
      simp only [bind_assoc]
      congr 1
      funext ignored
      congr 1
      funext p
      congr 1
      funext ignored
      congr 1
      funext released
      congr 1
      funext selected
      split
      · simp only [bind_assoc]
        congr 1
        funext ignored
        split <;> simp only [bind_assoc,pure_bind] <;> rfl
      · rfl

inductive Arm where
  | purge
  | overflow
  | finalRelease
  deriving DecidableEq

inductive Event where
  | purge (pid : PeerId) (run : WGRunWitness Unit)
  | overflow (pid : PeerId) (run : WGRunWitness Unit)
  | release (peer : Option PeerId) (run : WGRunWitness (Option (PeerId × Peer)))

/-- A nonfinal reference decrement is not a staged disposal. -/
def Event.arm : Event → Option Arm
  | .purge _ _ => some .purge
  | .overflow _ _ => some .overflow
  | .release _ r => if r.value.isSome then some .finalRelease else none

def Event.Valid : Event → Prop
  | .purge pid r => r.Valid (purgeStagedPackets pid)
  | .overflow pid r => r.Valid (Lifetimes.xmitTrim pid)
  | .release peer r => r.Valid (releaseCut peer)

def purgeObserved (pid : PeerId) : WGPrefix Event Unit :=
  receiptWGObserved (liftWGPrefix (purgeStagedPackets pid)) (.purge pid)

def overflowObserved (pid : PeerId) : WGPrefix Event Unit :=
  receiptWGObserved (liftWGPrefix (Lifetimes.xmitTrim pid)) (.overflow pid)

def releaseObserved (peer : Option PeerId) : WGPrefix Event Unit := do
  match ← receiptWGObserved (liftWGPrefix (releaseCut peer)) (.release peer) with
  | none => pure ()
  | some (pid,p) => liftWGPrefix (releaseFinish pid p)

theorem purge_erases (pid : PeerId) :
    ErasesStatePrefix (purgeObserved pid) (purgeStagedPackets pid) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem overflow_erases (pid : PeerId) :
    ErasesStatePrefix (overflowObserved pid) (Lifetimes.xmitTrim pid) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem release_erases (peer : Option PeerId) :
    ErasesStatePrefix (releaseObserved peer) (peerPut peer) := by
  rw [release_factor]
  unfold releaseObserved
  apply erasesStatePrefix_bind (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
  intro result
  cases result with
  | none => exact erasesStatePrefix_pure _
  | some pair => exact erasesStatePrefix_lift _

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal
