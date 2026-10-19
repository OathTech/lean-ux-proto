import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalSource

/-! Retain the original peer-access observer at the actual counted release
cut. The subsequent timer invariant and retirement remain a separate suffix. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PeerSource
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option pp.structureInstances false

structure Ops (m : Type → Type) where
  step : {α : Type} → WG.M α → m α
  read : PeerId → m Peer
  write : PeerId → Peer → m Unit
  erase : PeerId → Nat → m Unit

def native : Ops WG.M where
  step := id
  read := getPeer
  write := setPeer
  erase := fun pid dropped => modifyDev fun d =>
    {d with txDropped := d.txDropped + dropped, peers := d.peers.erase pid}

def peers : Ops (WGPrefix Peers.PeerEvent) where
  step := liftWGPrefix
  read := Peers.getPeerPrefix
  write := Peers.setPeerPrefix
  erase := Peers.erasePeerPrefix

def cutWith [Monad m] (o : Ops m) (peer : Option PeerId) : m (Option (PeerId × Peer)) := do
  if ← o.step (branch .peerPutNull peer.isNone) then return none
  let some pid := peer | o.step (invariant "unreachable")
  o.step (requireNotPending pid "a reference count the handshake worker also changes")
  let p ← o.read pid
  o.write pid {p with refcount := p.refcount - 1}
  if ← o.step (branch .peerKrefPutReleased (← o.step (refcountDecAndTest p.refcount))) then
    o.step (indexRemove (.handshake pid))
    if p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty then
      o.step (invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)")
    o.erase pid p.staged.length
    return some (pid,p)
  return none

def putWith [Monad m] (o : Ops m) (peer : Option PeerId) : m Unit := do
  match ← cutWith o peer with
  | none => pure ()
  | some (pid,p) => o.step (releaseFinish pid p)

theorem cut_native (peer : Option PeerId) : cutWith native peer = releaseCut peer := by
  unfold cutWith releaseCut native
  simp only [id]
  rfl

theorem put_native (peer : Option PeerId) : putWith native peer = peerPut peer := by
  rw [release_factor]
  unfold putWith
  rw [cut_native]
  rfl

private theorem lift_bind (a : WG.M α) (f : α → WG.M β) :
    (liftWGPrefix (a >>= f) : WGPrefix E β) =
      (liftWGPrefix a >>= fun x => liftWGPrefix (f x)) := by
  funext w ambient h
  change runWGPrefix (liftWGPrefix (_ >>= _)) w ambient h =
    runWGPrefix (liftWGPrefix _ >>= _) w ambient h
  simp only [runWGPrefix,runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift,StateT.run_bind]
  cases run : (a.run w).run ambient with
  | error _ => rfl
  | ok out => rcases out with ⟨⟨x,v⟩,b⟩; rfl

private theorem lift_pure (x : α) :
    (liftWGPrefix (pure x) : WGPrefix E α) = pure x := rfl

/-- The source factor preserves every C1 peer read, write and release event,
as well as the original outcome. No lifetime observer is replaced by erasure. -/
theorem put_peers (peer : Option PeerId) : putWith peers peer = Peers.peerPutPrefix peer := by
  unfold putWith cutWith peers Peers.peerPutPrefix releaseFinish
  simp only [bind_assoc]
  congr 1
  funext empty
  split
  · rfl
  · cases peer with
    | none => rfl
    | some pid =>
      simp only [requireNotPending, Peers.requireNotPendingPrefix, lift_pure, pure_bind, bind_assoc]
      congr 1
      funext p
      congr 1
      funext ignored
      congr 1
      funext count
      congr 1
      funext released
      split
      · simp only [bind_assoc]
        congr 1
        funext ignored
        split <;> simp only [bind_assoc,pure_bind]
        all_goals
          congr 1
          funext ignored
          split <;> simp_all only [lift_bind]
      · rfl

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PeerSource
