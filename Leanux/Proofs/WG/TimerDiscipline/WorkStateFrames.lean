import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource
import Leanux.Proofs.WG.Index.Insert

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Insertion changes the table, but neither queued work nor peer pending flags. -/
theorem indexInsert_queueWorkView (owner : IndexOwner) (pid : PeerId)
    (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ indexInsert owner
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [queueWorkAt, queueWorkKernel, workQueues, hd] at pre
  | some d =>
    obtain ⟨after, fresh⟩ := Index.indexInsert_exact owner d w result final hd run
    simpa [queueWorkAt, queueWorkKernel, workQueues, after, hd] using pre

/-- Queue/pending variant of shared Keypairs/Frames/WGTransitions.setChain_spec.
Factoring the original private two-accessor operation keeps creation's VC local. -/
theorem setChain_spec_queue_variant (pid : PeerId) (ck hash : List UInt8)
    (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄
      (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  noise_vcgen [_private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [queueWorkAt, queueWorkKernel, workQueues, Option.bind_map,
    Function.comp_def, Std.TreeMap.getElem?_insert]

theorem createInitiation_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ createInitiation pid
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  let P := fun k : Kernel => queueWorkKernel k pid = (some queue, some pending)
  have hh := hidden_kernel_spec P
  have hg := generatePublic_kernel_spec P
  have he := messageEphemeral_kernel_spec P
  have hd := mixDh_kernel_spec P
  have hs := mixPrecomputedDh_kernel_spec P
  have hi := fun owner => indexInsert_queueWorkView owner pid queue pending
  have hc := fun ck hash => setChain_spec_queue_variant pid ck hash queue pending
  noise_vcgen [createInitiation,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, hc, hh, hg, he, hd, hs, hi]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [P, queueWorkAt, queueWorkKernel, workQueues, Option.map_map, Option.bind_map,
    Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals try (cases queue <;> simp_all)
  all_goals grind

theorem addMacToPacket_queueWorkView (pid : PeerId) (msg : List UInt8)
    (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ addMacToPacket pid msg
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  have hh := hiddenClock64_kernel_spec
    (fun k => queueWorkKernel k pid = (some queue, some pending))
  mvcgen [addMacToPacket, Leanux.WG.andM, branchExpired, birthdateTest, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, branchCmp, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [queueWorkAt, queueWorkKernel, workQueues, Option.map_map, Option.bind_map,
    Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals try (cases queue <;> simp_all)
  all_goals grind

theorem modPeerTimer_queueWorkView (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ modPeerTimer site pid timer delay
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  have hh := hidden_kernel_spec (fun k => queueWorkKernel k pid = (some queue, some pending))
  mvcgen [modPeerTimer, callerJiffies, modPeerTimerGuard, Leanux.WG.andM, armTimer,
    hiddenJiffies, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, branchCmp, invariant, unsupported, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [queueWorkAt, queueWorkKernel, workQueues, Peer.setTimer, Option.bind_map,
    Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals try (cases queue <;> simp_all)
  all_goals grind

theorem traversal_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ timersTraversal pid
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  have hm := fun delay => modPeerTimer_queueWorkView .timerJiffiesTraversal pid
    .persistentKeepalive delay queue pending
  have hm' (delay : Nat) :
      ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄
        (discard (modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive delay) : M Unit)
        ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
    simpa [Functor.discard, Functor.mapConst] using (map_result_spec (fun _ : Bool => PUnit.unit) _ _ _ (hm delay))
  simp only [timersTraversal]
  mvcgen [getPeer, getDev, getK, branchCmp, invariant, hm']
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [queueWorkAt, queueWorkKernel]
  all_goals exact hm' _ _ (by simp)

theorem delKeepalive_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ timersAnyAuthenticatedPacketSent pid
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  mvcgen [timersAnyAuthenticatedPacketSent, delTimer, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [queueWorkAt, queueWorkKernel, workQueues, Peer.setTimer, Option.bind_map,
    Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals try (cases queue <;> simp_all)
  all_goals grind

theorem initiationArmPrefix_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ initiationArmPrefix pid
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  have hc := createInitiation_queueWorkView pid queue pending
  have hm := fun msg => addMacToPacket_queueWorkView pid msg queue pending
  have ht := traversal_queueWorkView pid queue pending
  have hd := delKeepalive_queueWorkView pid queue pending
  have hs := fun bytes => sendBufferToPeer_queueWorkView pid bytes (some queue, some pending)
  have hh := hiddenClock64_kernel_spec
    (fun k => queueWorkKernel k pid = (some queue, some pending))
  mvcgen [initiationArmPrefix, branchExpired, birthdateTest, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, branchCmp, invariant, hc, hm, ht, hd, hs, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [queueWorkAt, queueWorkKernel, workQueues, Option.map_map, Option.bind_map,
    Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals try (cases queue <;> simp_all)
  all_goals grind only

theorem timersHandshakeInitiated_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    ⦃fun w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ timersHandshakeInitiated pid
      ⦃⇓? _ w => ⌜queueWorkAt w pid = (some queue, some pending)⌝⦄ := by
  let P := fun k : Kernel => queueWorkKernel k pid = (some queue, some pending)
  have hh := hidden_kernel_spec P
  have hj := jitter_bounded P
  mvcgen [timersHandshakeInitiated, callerJiffies, hiddenJiffies, modPeerTimerGuard,
    Leanux.WG.andM, armTimer, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, invariant, unsupported, hh, hj]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [P, queueWorkAt, queueWorkKernel, workQueues, Peer.setTimer,
    Option.bind_map, Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals try (cases queue <;> simp_all)
  all_goals grind only

theorem sendHandshakeInitiation_queueWorkView (pid : PeerId) (queue : WorkQueues) (pending : Bool) :
    Ensures (sendHandshakeInitiation pid)
      (fun w => queueWorkAt w pid = (some queue, some pending))
      (fun _ w => queueWorkAt w pid = (some queue, some pending)) := by
  rw [sendInitiation_arm_source, ensures_iff]
  have hp := initiationArmPrefix_queueWorkView pid queue pending
  have ht := timersHandshakeInitiated_queueWorkView pid queue pending
  mvcgen [hp, ht]


/-- Projections retain every prior work-state interface. -/
theorem indexInsert_workView (owner : IndexOwner) (pid : PeerId)
    (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ indexInsert owner
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork (indexInsert owner) pid
    (indexInsert_queueWorkView owner pid) queue pending

theorem createInitiation_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ createInitiation pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork (createInitiation pid) pid
    (createInitiation_queueWorkView pid) queue pending

theorem addMacToPacket_workView (pid : PeerId) (msg : List UInt8)
    (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ addMacToPacket pid msg
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork (addMacToPacket pid msg) pid
    (addMacToPacket_queueWorkView pid msg) queue pending

theorem modPeerTimer_workView (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ modPeerTimer site pid timer delay
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork (modPeerTimer site pid timer delay) pid
    (modPeerTimer_queueWorkView site pid timer delay) queue pending

theorem traversal_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ timersTraversal pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork (timersTraversal pid) pid
    (traversal_queueWorkView pid) queue pending

theorem delKeepalive_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ timersAnyAuthenticatedPacketSent pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork (timersAnyAuthenticatedPacketSent pid) pid
    (delKeepalive_queueWorkView pid) queue pending

theorem initiationArmPrefix_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ initiationArmPrefix pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork (initiationArmPrefix pid) pid
    (initiationArmPrefix_queueWorkView pid) queue pending

theorem timersHandshakeInitiated_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    ⦃fun w => ⌜workAt w pid = (some queue, some pending)⌝⦄ timersHandshakeInitiated pid
      ⦃⇓? _ w => ⌜workAt w pid = (some queue, some pending)⌝⦄ := by
  exact work_frame_of_queueWork (timersHandshakeInitiated pid) pid
    (timersHandshakeInitiated_queueWorkView pid) queue pending

theorem sendHandshakeInitiation_workView (pid : PeerId) (queue : List PeerId) (pending : Bool) :
    Ensures (sendHandshakeInitiation pid)
      (fun w => workAt w pid = (some queue, some pending))
      (fun _ w => workAt w pid = (some queue, some pending)) := by
  rw [ensures_iff]
  exact work_frame_of_queueWork (sendHandshakeInitiation pid) pid
    (fun queues flag => (ensures_iff _ _ _).mp (sendHandshakeInitiation_queueWorkView pid queues flag)) queue pending

theorem retained_peerPut_workView (pid : PeerId) (identity attempts refs : Nat)
    (queue : List PeerId) (pending : Bool) (retained : 1 < refs) :
    Ensures (peerPut (some pid))
      (fun w => workerAt w pid = some (identity, attempts, refs) ∧
        workAt w pid = (some queue, some pending))
      (fun _ w => workAt w pid = (some queue, some pending)) := by
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [workerAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [workerAt, peerAt, hd, hp] at pre
    | some p =>
      have hv : workerView p = (identity, attempts, refs) := by
        simpa [workerAt, peerAt, hd, hp] using pre.1
      have hr : p.refcount = refs := congrArg (fun x => x.2.2) hv
      have last : p.refcount ≠ 1 := by omega
      obtain ⟨out, after, execution, device⟩ := Index.peerPut_exact pid d p hp (by omega) w hd
      rw [run] at execution
      cases execution
      simpa [workAt, workKernel, device, hd, hp, Index.releasedPeerDevice, last,
        Std.TreeMap.getElem?_insert] using pre.2

theorem handshakeSendWorker_workView (pid : PeerId) (identity attempts refs : Nat)
    (queue : List PeerId) (pending : Bool) (retained : 1 < refs) :
    Ensures (handshakeSendWorker pid)
      (fun w => workerAt w pid = some (identity, attempts, refs) ∧
        workAt w pid = (some queue, some pending))
      (fun _ w => workAt w pid = (some queue, some pending)) := by
  intro w result final pre run
  change ((sendHandshakeInitiation pid).run w >>= fun out =>
    (peerPut (some pid)).run out.2) = .ok (result, final) at run
  cases hs : (sendHandshakeInitiation pid).run w with
  | error e => rw [hs] at run; cases run
  | ok pair =>
    obtain ⟨u, middle⟩ := pair
    rw [hs] at run
    have worker := sendHandshakeInitiation_workerView pid (identity, attempts, refs)
      w u middle pre.1 hs
    have work := sendHandshakeInitiation_workView pid queue pending w u middle pre.2 hs
    exact retained_peerPut_workView pid identity attempts refs queue pending retained
      middle result final ⟨worker, work⟩ run

end Leanux.Proofs.WG.TimerDiscipline
