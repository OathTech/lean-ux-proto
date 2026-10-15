import Leanux.Proofs.WG.TimerDiscipline.Jitter
import Leanux.Proofs.WG.TimerDiscipline.SendBufferFrame

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem traversal_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ timersTraversal pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [initiationAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [initiationAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : initiationView p = v := by simpa [initiationAt, peerAt, hd, hp] using pre
      have effect := timersTraversal_effect pid d p hp w result final hd run
      split at effect
      · obtain ⟨expiry, peer⟩ := effect
        simpa [initiationAt, peer, initiationView, Peer.setTimer] using hv
      · simpa [initiationAt, effect] using hv

theorem delKeepalive_initiationView (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ timersAnyAuthenticatedPacketSent pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  mvcgen [timersAnyAuthenticatedPacketSent, delTimer, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [initiationAt, initiationView, peerAt, Peer.setTimer,
    Option.bind_map, Function.comp_def, Std.TreeMap.getElem?_insert]

theorem initiationArmPrefix_view (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ initiationArmPrefix pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  have hc := createInitiation_view pid v
  have hm := fun msg => addMacToPacket_view pid msg v
  have ht := traversal_initiationView pid v
  have hd := delKeepalive_initiationView pid v
  have hs := fun bytes => sendBufferToPeer_spec_initiation_variant pid bytes v
  have hh := hiddenClock64_kernel_spec
    (fun k => ((k.wg.bind fun d => d.peers[pid]?).map initiationView) = some v)
  mvcgen [initiationArmPrefix, branchExpired, birthdateTest, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, branchCmp, invariant, hc, hm, ht, hd, hs, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [initiationAt, initiationView, peerAt, Option.bind_map,
    Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals grind only

abbrev WorkerView := Nat × Nat × Nat

def workerView (p : Peer) : WorkerView := (p.internalId, p.timerHandshakeAttempts, p.refcount)
def workerAt (w : World) (pid : PeerId) : Option WorkerView := (peerAt w pid).map workerView

theorem timersHandshakeInitiated_workerView (pid : PeerId) (v : WorkerView) :
    ⦃fun w => ⌜workerAt w pid = some v⌝⦄ timersHandshakeInitiated pid
      ⦃⇓? _ w => ⌜workerAt w pid = some v⌝⦄ := by
  let P := fun k : Kernel => ((k.wg.bind fun d => d.peers[pid]?).map workerView) = some v
  have hh := hidden_kernel_spec P
  have hj := jitter_bounded P
  mvcgen [timersHandshakeInitiated, callerJiffies, hiddenJiffies, modPeerTimerGuard,
    Leanux.WG.andM, armTimer, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, invariant, unsupported, hh, hj]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [P, workerAt, workerView, peerAt, Peer.setTimer,
    Option.bind_map, Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals grind only

end Leanux.Proofs.WG.TimerDiscipline
