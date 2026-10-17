import Leanux.Proofs.WG.Config.LiveRemovalSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Relate both projected outcomes from the same actual entry states. The
prefix is observed on that entry, not on a state reconstructed from its view. -/
def RemovalJointObserves {α β : Type} (probe : WG.M α) (action : WG.M β)
    (P : Campaign2.Snapshot → Prop)
    (Q : Campaign2.Outcome α → Campaign2.Outcome β → Prop) : Prop :=
  ∀ g ambient, P (Campaign2.snapshot g ambient) →
    Q (Campaign2.observeResult ((probe.run g).run ambient))
      (Campaign2.observeResult ((action.run g).run ambient))

/-- Actual guard, clear and timer prefix; the captured device is read between
clear and timers, and the outcome snapshot is the actual post-timer state. -/
def removalAfterDeadPrefix (pid : PeerId) : WG.M Device := do
  removalDeadGuard pid
  keypairsClear pid
  let cleared ← getDev
  timersStop pid
  pure cleared

/-- Actual non-null branch and death prefix followed by the same cleanup cut. -/
def removalLivePrefix (pid : PeerId) : WG.M Device := do
  let _ ← branch .peerRemoveNull false
  peerMakeDead pid
  removalAfterDeadPrefix pid

/-- The clear/timer witness is tied to the prefix outcome. Its actual last
step supplies the diagnostic site; success retains the original exact effect. -/
def LiveRemovalOutcomes (pid : PeerId) (d : Device) (p : Peer)
    (probe : Campaign2.Outcome Device) (out : Campaign2.Outcome Unit) : Prop :=
  ∃ cleared timed,
    probe = .ok (cleared, timed) ∧
    ClearRun pid d [.next, .previous, .current] cleared ∧
    cleared.peers[pid]? = some (emptyKeysPeer p) ∧
    timed.wg.device = some (deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer p)) ∧
    let finalDevice := deleteTimersDevice PeerTimer.all cleared pid (emptyKeysPeer p)
    if !finalDevice.encryptQueue.empty || !finalDevice.decryptQueue.empty ||
        !finalDevice.txWorkQueue.isEmpty || finalDevice.peers.toList.any (·.2.napiScheduled) then
      out = .error (.outsideDomain (match timed.ambient.steps.back? with
        | some step => s!"{step.decision.info.file}:{step.decision.info.line}"
        | none => "syscall entry")
        "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")
    else match Index.peerReleaseRefusal pid (quietCleanupPeer p) with
      | some stop => out = .error stop
      | none => ∃ final, out = .ok ((), final) ∧
          final.wg.device = some (removedAfterClear cleared pid p) ∧
          LiveRemovalEffect pid d p (removedAfterClear cleared pid p)


end Leanux.Proofs.WG.Config
