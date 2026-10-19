import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementFrames

/-! Release prefixes use the actual cached peer, refcount result, and index
unhash position. Stopped tests retain the decremented world; a failed queue
guard retains the unlinked world, before any counted staged erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000

abbrev entryClock (a : Ambient) : Ambient := branchClock a .peerPutNull false

def decDevice (pid : PeerId) (p : Peer) (d : Device) : Device :=
  {d with peers := d.peers.insert pid {p with refcount := p.refcount-1}}

def indexDevice (pid : PeerId) (p : Peer) (d : Device) : Device :=
  {decDevice pid p d with indexTable := d.indexTable.filter (fun e=>!(e.owner == .handshake pid))}

def indexWorld (pid : PeerId) (p : Peer) (d : Device) (w : WGWorld) : WGWorld :=
  unlinked pid (decDevice pid p d) (decremented pid p d w)

def finalWorld (pid : PeerId) (p : Peer) (d : Device) (w : WGWorld) : WGWorld :=
  erased pid p (indexDevice pid p d) (indexWorld pid p d w)

def indexClock (pid : PeerId) (d : Device) (b : Ambient) : Ambient :=
  branchClock b .idxRemoveHashed (d.indexTable.any (fun e=>e.owner == .handshake pid))

theorem decrement_prefix (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((decrementTo (some pid)).run w).run a=
      .ok ((some (pid,p),decremented pid p d w),entryClock a) := by
  unfold decrementTo
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨_,_,_,read_some device resident,?_⟩
  dsimp only
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨_,_,_,decrement_run device,rfl⟩

theorem test_prefix (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((testTo (some pid)).run w).run a=
      ((testAmbient p.refcount).run (entryClock a)).map
        (fun (final,b)=>((some (pid,p,final),decremented pid p d w),b)) := by
  unfold testTo
  simp only [StateT.run_bind,decrement_prefix device resident]
  change ((do let final ← test p; pure (some (pid,p,final)) : WG.M Tested).run _).run _=_
  simp only [StateT.run_bind,test_run]
  cases result : ((testAmbient p.refcount).run (entryClock a)) with
  | error stop => rfl
  | ok out => obtain ⟨final,b⟩:=out; rfl

theorem unlink_prefix (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (tested : (testAmbient p.refcount).run (entryClock a)=.ok (true,b)) :
    ((unlinkTo (some pid)).run w).run a=
      .ok ((some (pid,p),indexWorld pid p d w),indexClock pid d b) := by
  unfold unlinkTo
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨some (pid,p,true),decremented pid p d w,b,?_,?_⟩
  · rw [test_prefix device resident,tested]; rfl
  · dsimp only
    simp only [ite_true]
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨_,_,_,unlink_run (w:=decremented pid p d w) (d:=decDevice pid p d) rfl,rfl⟩

theorem erase_prefix (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (tested : (testAmbient p.refcount).run (entryClock a)=.ok (true,b))
    (quiet : queued p=false) :
    ((releaseCut (some pid)).run w).run a=
      .ok ((some (pid,p),finalWorld pid p d w),indexClock pid d b) := by
  rw [release_unlink_factor,MaterialOrigin.bind_ok_ambient]
  refine ⟨_,_,_,unlink_prefix device resident tested,?_⟩
  unfold eraseTail
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨(),indexWorld pid p d w,indexClock pid d b,?_,?_⟩
  · simp only [guard_run,quiet,Bool.false_eq_true,ite_false]
  · rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨_,_,_,erase_run (w:=indexWorld pid p d w) (d:=indexDevice pid p d) rfl,rfl⟩

theorem read_stopped
    (failed : ((readRelease peer).run w).run a=.error stop) :
    ((releaseCut peer).run w).run a=.error stop := by
  rw [release_read_factor]
  simp only [StateT.run_bind,failed]
  rfl

theorem test_stopped (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (failed : (testAmbient p.refcount).run (entryClock a)=.error stop) :
    ((releaseCut (some pid)).run w).run a=.error stop ∧
    ((test p).run (decremented pid p d w)).run (entryClock a)=.error stop := by
  constructor
  · rw [release_test_factor]
    simp only [StateT.run_bind,test_prefix device resident,failed,Except.map]
    rfl
  · rw [test_run,failed]; rfl

theorem nonfinal (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (tested : (testAmbient p.refcount).run (entryClock a)=.ok (false,b)) :
    ((releaseCut (some pid)).run w).run a=.ok ((none,decremented pid p d w),b) := by
  rw [release_test_factor]
  simp only [StateT.run_bind,test_prefix device resident,tested,Except.map]
  rfl

theorem queue_stopped (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (tested : (testAmbient p.refcount).run (entryClock a)=.ok (true,b))
    (busy : queued p=true) :
    let stop := Stop.invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)"
    ((releaseCut (some pid)).run w).run a=.error stop ∧
    ((queueGuard p).run (indexWorld pid p d w)).run (indexClock pid d b)=.error stop := by
  dsimp only
  constructor
  · rw [release_unlink_factor]
    simp only [StateT.run_bind,unlink_prefix device resident tested]
    change ((eraseTail (some (pid,p))).run (indexWorld pid p d w)).run (indexClock pid d b)=_
    unfold eraseTail
    simp only [StateT.run_bind,guard_run,busy,ite_true]
    rfl
  · simp only [guard_run,busy,ite_true]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
