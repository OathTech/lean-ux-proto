import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointCoverage
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseFrames

/-! The nested release's original access-bearing stages. The operations are
those of PeerSource.cutWith, so read/write receipts remain at their actual
positions. The captured entry for the later counted receipt is not reset. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.StagedDisposal PeerRetirement
abbrev Stage := PeerRetirement.Points.Stage
variable {m : Type → Type}

def readWith [Monad m] (o : PeerSource.Ops m) (peer : Option PeerId) : m Cached := do
  if ← o.step (branch .peerPutNull peer.isNone) then return none
  let some pid := peer | o.step (invariant "unreachable")
  o.step (requireNotPending pid "a reference count the handshake worker also changes")
  let p ← o.read pid
  pure (some (pid,p))

def testWith [Monad m] (o : PeerSource.Ops m) (p : Peer) : m Bool := do
  let released ← o.step (refcountDecAndTest p.refcount)
  o.step (branch .peerKrefPutReleased released)

def guardWith [Monad m] (o : PeerSource.Ops m) (p : Peer) : m Unit := do
  if queued p then
    o.step (invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)")

def eraseAfter [Monad m] (o : PeerSource.Ops m) : Cached → m Cached
  | none=>pure none
  | some (pid,p)=>do o.erase pid p.staged.length;pure (some (pid,p))

def eraseTail [Monad m] (o : PeerSource.Ops m) : Cached → m Cached
  | none=>pure none
  | some (pid,p)=>do guardWith o p;eraseAfter o (some (pid,p))

def testTail [Monad m] (o : PeerSource.Ops m) : Tested → m Cached
  | none=>pure none
  | some (pid,p,final)=>if final then do o.step (indexRemove (.handshake pid));eraseTail o (some (pid,p)) else pure none

def decrementTail [Monad m] (o : PeerSource.Ops m) : Cached → m Cached
  | none=>pure none
  | some (pid,p)=>do let final ← testWith o p;testTail o (some (pid,p,final))

def readTail [Monad m] (o : PeerSource.Ops m) : Cached → m Cached
  | none=>pure none
  | some (pid,p)=>do o.write pid {p with refcount:=p.refcount-1};decrementTail o (some (pid,p))

def decrementTo [Monad m] (o : PeerSource.Ops m) (peer : Option PeerId) : m Cached := do
  let cached ← readWith o peer
  match cached with
  | none=>pure none
  | some (pid,p)=>o.write pid {p with refcount:=p.refcount-1};pure cached

def testTo [Monad m] (o : PeerSource.Ops m) (peer : Option PeerId) : m Tested := do
  match ← decrementTo o peer with
  | none=>pure none
  | some (pid,p)=>let final ← testWith o p;pure (some (pid,p,final))

def unlinkTo [Monad m] (o : PeerSource.Ops m) (peer : Option PeerId) : m Cached := do
  match ← testTo o peer with
  | none=>pure none
  | some (pid,p,final)=>if final then o.step (indexRemove (.handshake pid));pure (some (pid,p)) else pure none

def checkedTo [Monad m] (o : PeerSource.Ops m) (peer : Option PeerId) : m Cached := do
  let cached ← unlinkTo o peer
  match cached with
  | none=>pure none
  | some (_,p)=>guardWith o p;pure cached

def prefixAt [Monad m] (o : PeerSource.Ops m) (stage : Stage) (peer : Option PeerId) : m stage.Result :=
  match stage with
  | .read=>readWith o peer
  | .decrement=>decrementTo o peer
  | .test=>testTo o peer
  | .unlink=>unlinkTo o peer
  | .checked=>checkedTo o peer

def tail [Monad m] (o : PeerSource.Ops m) (stage : Stage) : stage.Result → m Cached :=
  match stage with
  | .read=>readTail o
  | .decrement=>decrementTail o
  | .test=>testTail o
  | .unlink=>eraseTail o
  | .checked=>eraseAfter o

abbrev actual := AllocatedObligation.PeerRelease.ops

theorem read_factor (peer : Option PeerId) :
    PeerSource.cutWith actual peer=readWith actual peer >>= readTail actual := by
  unfold PeerSource.cutWith readWith
  simp only [bind_assoc]
  congr 1
  funext missing
  split
  · rfl
  · cases peer with
    | none=>rfl
    | some pid=>
      simp only [bind_assoc]
      congr 1
      funext ignored
      congr 1
      funext p
      simp only [pure_bind,readTail,decrementTail,testWith,testTail,eraseTail,eraseAfter,guardWith,bind_assoc]
      congr 1
      funext ignored
      congr 1
      funext count
      congr 1
      funext final
      cases final <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      congr 1
      funext ignored
      change (if queued p then do actual.step (invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)");actual.erase pid p.staged.length;pure (some (pid,p))
          else do actual.erase pid p.staged.length;pure (some (pid,p))) = _
      cases queued p <;> simp only [Bool.false_eq_true,ite_false,ite_true,pure_bind]

theorem decrement_factor (peer : Option PeerId) :
    PeerSource.cutWith actual peer=decrementTo actual peer >>= decrementTail actual := by
  rw [read_factor]
  simp only [decrementTo,bind_assoc]
  congr 1
  funext cached
  cases cached with
  | none=>rfl
  | some pair=>obtain ⟨pid,p⟩:=pair; simp only [readTail,bind_assoc,pure_bind]

theorem test_factor (peer : Option PeerId) :
    PeerSource.cutWith actual peer=testTo actual peer >>= testTail actual := by
  rw [decrement_factor]
  simp only [testTo,bind_assoc]
  congr 1
  funext cached
  cases cached with
  | none=>rfl
  | some pair=>obtain ⟨pid,p⟩:=pair; simp only [decrementTail,bind_assoc,pure_bind]

theorem unlink_factor (peer : Option PeerId) :
    PeerSource.cutWith actual peer=unlinkTo actual peer >>= eraseTail actual := by
  rw [test_factor]
  simp only [unlinkTo,bind_assoc]
  congr 1
  funext cached
  cases cached with
  | none=>rfl
  | some triple=>
    obtain ⟨pid,p,final⟩:=triple
    cases final <;> simp only [testTail,Bool.false_eq_true,ite_false,ite_true,pure_bind,bind_assoc]
    rfl

theorem checked_factor (peer : Option PeerId) :
    PeerSource.cutWith actual peer=checkedTo actual peer >>= eraseAfter actual := by
  rw [unlink_factor]
  simp only [checkedTo,bind_assoc]
  congr 1
  funext cached
  cases cached with
  | none=>rfl
  | some pair=>obtain ⟨pid,p⟩:=pair; simp only [eraseTail,bind_assoc,pure_bind]

theorem factor (stage : Stage) (peer : Option PeerId) :
    PeerSource.cutWith actual peer=prefixAt actual stage peer >>= tail actual stage := by
  cases stage with
  | read=>exact read_factor peer
  | decrement=>exact decrement_factor peer
  | test=>exact test_factor peer
  | unlink=>exact unlink_factor peer
  | checked=>exact checked_factor peer

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
