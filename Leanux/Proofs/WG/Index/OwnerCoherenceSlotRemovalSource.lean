import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalFrames
import Leanux.Proofs.WG.Config.LiveRemovalSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Actual post-dead removal retains coherence for every normal return under
entry slot coverage. No static key-reference budget or cleanup readiness is
assumed; all original refusal paths remain in the actual operation. -/
theorem peerRemoveAfterDead_slot_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (dead : p.isDead = true)
    (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (covered : LastOwnerCovered d pid p) :
    Campaign2.Ensures (peerRemoveAfterDead pid)
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient value final after pre run
  have device : g.dev = some d := pre.1
  let guarded := {ambient with steps := ambient.steps.push {
    decision := .peerRemoveNotDead, outcome := false, netRx := ambient.netRxSection}}
  have guardRun : ((Config.removalDeadGuard pid).run g).run ambient = .ok (((), g), guarded) := by
    simp [Config.removalDeadGuard, getPeer, getDev, device, resident, dead, branch, AmbientM.branch, guarded]
    rfl
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), after) =>
          ((next value).run middle).run after) := rfl
  have okBind {α β : Type} (x : α) (next : α → Except Stop β) :
      (Except.ok x >>= next) = next x := rfl
  cases clearRun : ((keypairsClear pid).run g).run guarded with
  | error stop =>
    rw [Config.peerRemoveAfterDead_source] at run
    simp only [bindRun,guardRun,okBind,clearRun] at run
    cases run
  | ok out =>
    rcases out with ⟨⟨u,clearedState⟩,clearAmbient⟩
    cases u
    obtain ⟨cleared,clearedDevice,steps⟩ :=
      keypairsClear_effect pid d p resident g guarded () clearedState clearAmbient device clearRun
    have clearedPeer : cleared.peers[pid]? = some (Config.emptyKeysPeer p) := by
      have hp := keypairsClear_peer pid p g guarded () clearedState clearAmbient
        (by simp [peerAt, device, resident]) clearRun
      simpa [peerAt, clearedDevice, Config.emptyKeysPeer] using hp
    have context := Config.clearRun_cleanupContext steps
    have sendCleared : cleared.sendWorkQueue = [] := (congrArg Prod.fst context).trans send
    have clearCleared : cleared.clearWorkQueue = [] := (congrArg (fun x => x.2.1) context).trans clear
    have countCleared : 0 < cleared.numPeers := by
      have eqCount := congrArg (fun x => x.2.2) context
      change cleared.numPeers = d.numPeers at eqCount
      rw [eqCount]
      exact count
    obtain ⟨u,timedState,timerAmbient,timerRun,timedDevice⟩ :=
      Config.timersStop_quiet_returns pid cleared (Config.emptyKeysPeer p) clearedPeer clearCleared
        clearedState clearAmbient clearedDevice
    cases u
    let timed := Config.deleteTimersDevice PeerTimer.all cleared pid (Config.emptyKeysPeer p)
    change timedState.dev = some timed at timedDevice
    have factor : ((peerRemoveAfterDead pid).run g).run ambient =
        ((do
          if !timed.encryptQueue.empty || !timed.decryptQueue.empty || !timed.txWorkQueue.isEmpty ||
              timed.peers.toList.any (·.2.napiScheduled) then
            unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)"
          drainHandshakeSendWq none
          Config.decrementPeerCount
          peerPut (some pid) : WG.M Unit).run timedState).run timerAmbient := by
      rw [Config.peerRemoveAfterDead_source]
      simp only [bindRun,guardRun,okBind,clearRun,timerRun]
      simp [getDev,timedDevice]
    rw [factor] at run
    cases crypt : (!timed.encryptQueue.empty || !timed.decryptQueue.empty || !timed.txWorkQueue.isEmpty ||
        timed.peers.toList.any (·.2.napiScheduled)) with
    | true =>
      simp only [crypt,ite_true] at run
      have impossible : (Except.error (.outsideDomain "" "") : Except Stop Unit) = .ok () := by
        cases value
        exact congrArg (fun outcome => match outcome with
          | .error _ => (Except.error (.outsideDomain "" "") : Except Stop Unit)
          | .ok _ => .ok ()) run
      cases impossible
    | false =>
      simp only [crypt,Bool.false_eq_true,ite_false] at run
      have tail := Config.removalAfterClear_returns pid cleared p clearedPeer live countCleared
        sendCleared clearCleared clearedState clearAmbient clearedDevice
      simp only [bindRun,timerRun,okBind] at tail
      let finish : WG.M Unit := do
        drainHandshakeSendWq none
        Config.decrementPeerCount
        peerPut (some pid)
      have finalRun : (finish.run timedState).run timerAmbient = .ok ((value,final),after) := run
      change (match peerReleaseRefusal pid (Config.quietCleanupPeer p) with
        | some stop => Campaign2.observeResult ((finish.run timedState).run timerAmbient) = .error stop
        | none => ∃ observed, Campaign2.observeResult ((finish.run timedState).run timerAmbient) =
            .ok ((),observed) ∧ observed.wg.device = some (Config.removedAfterClear cleared pid p)) at tail
      rw [finalRun] at tail
      cases refusal : peerReleaseRefusal pid (Config.quietCleanupPeer p) with
      | some stop =>
        rw [refusal] at tail
        cases tail
      | none =>
        simp only [refusal] at tail
        obtain ⟨observed,equal,found⟩ := tail
        have same : Campaign2.snapshot final after = observed :=
          (Prod.mk.inj (Except.ok.inj equal)).2
        rw [← same] at found
        intro current present
        rw [found] at present
        cases present
        exact removedAfterClear_owner_coherent pid d cleared p resident live
          (pre.2 d pre.1) covered steps clearedPeer

end Leanux.Proofs.WG.Index
