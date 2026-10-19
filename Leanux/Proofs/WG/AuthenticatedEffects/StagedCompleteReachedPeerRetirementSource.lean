import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontResidualReceipt
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompletePurgeSource

/-! Fixed prefixes of the original release and purge primitives. Release
charges and erases atomically, after decrement, refcount test and unhash;
purge charges before its separate queue-clear write. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000

abbrev Cached := Option (PeerId × Peer)
abbrev Tested := Option (PeerId × Peer × Bool)

def readRelease (peer : Option PeerId) : WG.M Cached := do
  if ← branch .peerPutNull peer.isNone then return none
  let some pid := peer | invariant "unreachable"
  requireNotPending pid "a reference count the handshake worker also changes"
  let p ← getPeer pid
  pure (some (pid,p))

def decrement (pid : PeerId) (p : Peer) : WG.M Unit :=
  setPeer pid {p with refcount := p.refcount-1}

def test (p : Peer) : WG.M Bool := do
  let released ← refcountDecAndTest p.refcount
  branch .peerKrefPutReleased released

def unlink (pid : PeerId) : WG.M Unit := liftIndex (indexRemove (.handshake pid))

def queued (p : Peer) : Bool :=
  p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty

def queueGuard (p : Peer) : WG.M Unit := do
  if queued p then
    invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)"

def erase (pid : PeerId) (p : Peer) : WG.M Unit :=
  modifyDev fun d => {d with txDropped := d.txDropped+p.staged.length, peers := d.peers.erase pid}

def eraseTail : Cached → WG.M Cached
  | none => pure none
  | some (pid,p) => do queueGuard p; erase pid p; pure (some (pid,p))

def testTail : Tested → WG.M Cached
  | none => pure none
  | some (pid,p,final) => if final then do unlink pid; eraseTail (some (pid,p)) else pure none

def decrementTail : Cached → WG.M Cached
  | none => pure none
  | some (pid,p) => do let final ← test p; testTail (some (pid,p,final))

def readTail : Cached → WG.M Cached
  | none => pure none
  | some (pid,p) => do decrement pid p; decrementTail (some (pid,p))

theorem release_read_factor (peer : Option PeerId) :
    releaseCut peer=readRelease peer >>= readTail := by
  have lift (action : IndexM Unit) : (liftM action : WG.M Unit)=liftIndex action := rfl
  unfold releaseCut readRelease
  simp only [bind_assoc]
  congr 1
  funext missing
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
      simp only [pure_bind,readTail,decrement,decrementTail,test,testTail,eraseTail,queueGuard,queued,erase,unlink,lift,bind_assoc]
      by_cases busy : (p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty)=true
      all_goals simp [busy]

def decrementTo (peer : Option PeerId) : WG.M Cached := do
  let cached ← readRelease peer
  match cached with
  | none => pure none
  | some (pid,p) => decrement pid p; pure cached

def testTo (peer : Option PeerId) : WG.M Tested := do
  match ← decrementTo peer with
  | none => pure none
  | some (pid,p) => let final ← test p; pure (some (pid,p,final))

def unlinkTo (peer : Option PeerId) : WG.M Cached := do
  match ← testTo peer with
  | none => pure none
  | some (pid,p,final) =>
    if final then unlink pid; pure (some (pid,p)) else pure none

theorem release_decrement_factor (peer : Option PeerId) :
    releaseCut peer=decrementTo peer >>= decrementTail := by
  rw [release_read_factor]
  simp only [decrementTo,bind_assoc]
  congr 1
  funext cached
  cases cached with
  | none => rfl
  | some pair => obtain ⟨pid,p⟩:=pair; simp only [readTail,bind_assoc,pure_bind]

theorem release_test_factor (peer : Option PeerId) :
    releaseCut peer=testTo peer >>= testTail := by
  rw [release_decrement_factor]
  simp only [testTo,bind_assoc]
  congr 1
  funext cached
  cases cached with
  | none => rfl
  | some pair => obtain ⟨pid,p⟩:=pair; simp only [decrementTail,bind_assoc,pure_bind]

theorem release_unlink_factor (peer : Option PeerId) :
    releaseCut peer=unlinkTo peer >>= eraseTail := by
  rw [release_test_factor]
  simp only [unlinkTo,bind_assoc]
  congr 1
  funext cached
  cases cached with
  | none => rfl
  | some triple =>
    obtain ⟨pid,p,final⟩:=triple
    cases final <;> simp only [testTail,Bool.false_eq_true,ite_false,ite_true,pure_bind,bind_assoc]
    rfl

def purgeCharge (p : Peer) : WG.M Unit :=
  modifyDev fun d => {d with txDropped := d.txDropped+p.staged.length}

def purgeClear (pid : PeerId) (p : Peer) : WG.M Unit := setPeer pid {p with staged := []}

def purgeChargeTo (pid : PeerId) : WG.M Peer := do
  let p ← getPeer pid
  purgeCharge p
  pure p

theorem purge_factor (pid : PeerId) :
    purgeStagedPackets pid=purgeChargeTo pid >>= purgeClear pid := by
  simp only [purgeStagedPackets,purgeChargeTo,purgeCharge,purgeClear,bind_assoc,pure_bind]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
