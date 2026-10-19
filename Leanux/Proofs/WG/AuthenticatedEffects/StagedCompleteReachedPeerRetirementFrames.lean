import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementSource

/-! The exact worlds at the primitive mutation boundaries. Ambient refcount
and queue guards remain actual source calls, including their stopped arms. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000

def branchClock (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
  {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}

def decremented (pid : PeerId) (p : Peer) (d : Device) (w : WGWorld) : WGWorld :=
  {w with dev := some {d with peers := d.peers.insert pid {p with refcount := p.refcount-1}}}

def unlinked (pid : PeerId) (d : Device) (w : WGWorld) : WGWorld :=
  {w with dev := some {d with indexTable := d.indexTable.filter (fun e => !(e.owner == .handshake pid))}}

def erased (pid : PeerId) (p : Peer) (d : Device) (w : WGWorld) : WGWorld :=
  {w with dev := some {d with txDropped := d.txDropped+p.staged.length,peers := d.peers.erase pid}}

def charged (p : Peer) (d : Device) (w : WGWorld) : WGWorld :=
  {w with dev := some {d with txDropped := d.txDropped+p.staged.length}}

def cleared (pid : PeerId) (p : Peer) (d : Device) (w : WGWorld) : WGWorld :=
  {w with dev := some {d with txDropped := d.txDropped+p.staged.length,peers := d.peers.insert pid {p with staged := []}}}

theorem read_some (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((readRelease (some pid)).run w).run a=
      .ok ((some (pid,p),w),branchClock a .peerPutNull false) := by
  simp [readRelease,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,resident,branchClock]

theorem read_none (w : WGWorld) (a : Ambient) :
    ((readRelease none).run w).run a=.ok ((none,w),branchClock a .peerPutNull true) := by
  simp [readRelease,branch,AmbientM.branch,branchClock]

theorem decrement_run (device : w.dev=some d) :
    ((decrement pid p).run w).run a=.ok (((),decremented pid p d w),a) := by
  simp [decrement,setPeer,modifyDev,device,decremented]

def testAmbient (count : Nat) : AmbientM Bool := do
  let final ← refcountDecAndTest count
  AmbientM.branch .peerKrefPutReleased final

theorem test_run (p : Peer) (w : WGWorld) (a : Ambient) :
    ((test p).run w).run a=
      ((testAmbient p.refcount).run a).map (fun (value,b)=>((value,w),b)) := by
  cases count : p.refcount with
  | zero => simp [test,testAmbient,refcountDecAndTest,count,branch,branchCmp,
      AmbientM.branch,AmbientM.branchCmp,unsupported,AmbientM.unsupported,Except.map] <;> rfl
  | succ n =>
    cases n with
    | zero => simp [test,testAmbient,refcountDecAndTest,count,branch,branchCmp,
        AmbientM.branch,AmbientM.branchCmp,Except.map] <;> rfl
    | succ n => simp [test,testAmbient,refcountDecAndTest,count,branch,branchCmp,
        AmbientM.branch,AmbientM.branchCmp,Except.map] <;> rfl


theorem unlink_run (device : w.dev=some d) :
    ((unlink pid).run w).run a=
      .ok (((),unlinked pid d w),branchClock a .idxRemoveHashed (d.indexTable.any (fun e=>e.owner == .handshake pid))) := by
  simp [unlink,indexRemove_eq,indexUnhash,liftIndex,getDev,modifyDev,device,
    branch,AmbientM.branch,unlinked,branchClock]

theorem guard_run (p : Peer) (w : WGWorld) (a : Ambient) :
    ((queueGuard p).run w).run a=
      if queued p then .error (.invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)")
      else .ok (((),w),a) := by
  by_cases busy : queued p=true <;> simp [queueGuard,busy,invariant,AmbientM.invariant] <;> rfl

theorem erase_run (device : w.dev=some d) :
    ((erase pid p).run w).run a=.ok (((),erased pid p d w),a) := by
  simp [erase,modifyDev,device,erased]

theorem charge_run (device : w.dev=some d) :
    ((purgeCharge p).run w).run a=.ok (((),charged p d w),a) := by
  simp [purgeCharge,modifyDev,device,charged]

theorem clear_run :
    ((purgeClear pid p).run (charged p d w)).run a=.ok (((),cleared pid p d w),a) := rfl

theorem decrement_geometry (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    Staged.stagedAt (decremented pid p d w) pid=Staged.stagedAt w pid ∧
    Staged.dropped (decremented pid p d w)=Staged.dropped w ∧
    ((decremented pid p d w).dev.bind (fun e=>e.peers[pid]?)).map Peer.refcount=some (p.refcount-1) := by
  simp [decremented,Staged.stagedAt,Staged.dropped,device,resident]

theorem unlink_geometry (device : w.dev=some d) :
    Staged.stagedAt (unlinked pid d w)=Staged.stagedAt w ∧
    Staged.dropped (unlinked pid d w)=Staged.dropped w := by
  constructor
  · funext q; simp [unlinked,Staged.stagedAt,device]
  · simp [unlinked,Staged.dropped,device]

theorem erase_geometry :
    Staged.stagedAt (erased pid p d w) pid=none ∧
    Staged.dropped (erased pid p d w)=some (d.txDropped+p.staged.length) := by
  simp [erased,Staged.stagedAt,Staged.dropped]

theorem charge_geometry (device : w.dev=some d) :
    Staged.stagedAt (charged p d w)=Staged.stagedAt w ∧
    Staged.dropped (charged p d w)=some (d.txDropped+p.staged.length) := by
  constructor
  · funext pid; simp [charged,Staged.stagedAt,device]
  · rfl

theorem clear_geometry :
    Staged.stagedAt (cleared pid p d w) pid=some (p.internalId,[]) ∧
    Staged.dropped (cleared pid p d w)=some (d.txDropped+p.staged.length) := by
  simp [cleared,Staged.stagedAt,Staged.dropped]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
