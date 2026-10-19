import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementRelease

/-! Exhaustive release classification follows the native source stages.
The two post-mutation failures retain their literal prefix worlds, rather
than reconstructing a world from a stopped endpoint. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000

inductive ReleaseCase : (peer : Option PeerId) → (w : WGWorld) → (a : Ambient) →
    Except Stop ((Cached × WGWorld) × Ambient) → Prop where
  | readStopped (failed : ((readRelease peer).run w).run a=.error stop) :
      ReleaseCase peer w a (.error stop)
  | null : ReleaseCase none w a (.ok ((none,w),branchClock a .peerPutNull true))
  | testStopped (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (failed : (testAmbient p.refcount).run (entryClock a)=.error stop) :
      ReleaseCase (some pid) w a (.error stop)
  | nonfinal (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (tested : (testAmbient p.refcount).run (entryClock a)=.ok (false,b)) :
      ReleaseCase (some pid) w a (.ok ((none,decremented pid p d w),b))
  | queueStopped (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (tested : (testAmbient p.refcount).run (entryClock a)=.ok (true,b))
      (busy : queued p=true) : ReleaseCase (some pid) w a
        (.error (.invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)"))
  | final (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (tested : (testAmbient p.refcount).run (entryClock a)=.ok (true,b))
      (quiet : queued p=false) : ReleaseCase (some pid) w a
        (.ok ((some (pid,p),finalWorld pid p d w),indexClock pid d b))

theorem ReleaseCase.literal (path : ReleaseCase peer w a result) :
    ((releaseCut peer).run w).run a=result := by
  cases path with
  | readStopped failed => exact read_stopped failed
  | null =>
    rw [release_read_factor]
    simp only [StateT.run_bind,read_none]
    rfl
  | testStopped device resident failed => exact (test_stopped device resident failed).1
  | nonfinal device resident tested => exact PeerRetirement.nonfinal device resident tested
  | queueStopped device resident tested busy => exact (queue_stopped device resident tested busy).1
  | final device resident tested quiet => exact erase_prefix device resident tested quiet

/-- This classification is derived for every invocation, without an assumed
normal return or a preselected successful internal cut. -/
theorem release_cases (peer : Option PeerId) (w : WGWorld) (a : Ambient) :
    ReleaseCase peer w a (((releaseCut peer).run w).run a) := by
  cases peer with
  | none =>
    have path : ReleaseCase none w a (.ok ((none,w),branchClock a .peerPutNull true)):=.null
    rw [path.literal]
    exact path
  | some pid =>
    cases device : w.dev with
    | none =>
      have failed : ((readRelease (some pid)).run w).run a=
          .error (.invariant "no WireGuard device in this trace's fixture") := by
        simp [readRelease,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,
          invariant,AmbientM.invariant]
        rfl
      rw [read_stopped failed]
      exact .readStopped failed
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        have failed : ((readRelease (some pid)).run w).run a=.error (.invariant s!"dangling peer {pid}") := by
          simp [readRelease,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,resident,
            invariant,AmbientM.invariant]
          rfl
        rw [read_stopped failed]
        exact .readStopped failed
      | some p =>
        cases tested : (testAmbient p.refcount).run (entryClock a) with
        | error stop =>
          rw [(test_stopped device resident tested).1]
          exact .testStopped device resident tested
        | ok out =>
          obtain ⟨final,b⟩:=out
          cases final with
          | false =>
            rw [PeerRetirement.nonfinal device resident tested]
            exact .nonfinal device resident tested
          | true =>
            cases busy : queued p with
            | false =>
              rw [erase_prefix device resident tested busy]
              exact .final device resident tested busy
            | true =>
              rw [(queue_stopped device resident tested busy).1]
              exact .queueStopped device resident tested busy

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
