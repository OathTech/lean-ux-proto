import Leanux.Proofs.WG.TransmitSecurity.DriverGroNeutral
import Leanux.Proofs.WG.TransmitSecurity.DriverNeutralCalls
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral

/-! The selection receipt factors an original source prefix. The resulting
driver still executes exactly the existing reservation observer. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxHeartbeats 800000

private theorem lift_bind (a : WG.M α) (f : α → WG.M β) :
    (liftWGPrefix (a >>= f) : WGPrefix E β) =
      (liftWGPrefix a >>= fun x => liftWGPrefix (f x)) := by
  funext wg ambient hist
  change runWGPrefix (liftWGPrefix (a >>= f)) wg ambient hist =
    runStatePrefix (liftWGPrefix a >>= fun x => liftWGPrefix (f x)) wg ambient hist
  rw [runWGPrefix_lift,runStatePrefix_bind]
  change (((a >>= f).run wg).run ambient,hist) = _
  simp only [liftWGPrefix,StateT.run_bind,runStatePrefix_lift]
  cases (a.run wg).run ambient with
  | error stop => rfl
  | ok out => rcases out with ⟨⟨x,w⟩,b⟩; rfl

private theorem lift_pure (x : α) : (liftWGPrefix (pure x) : WGPrefix E α) = pure x := rfl

private theorem lift_ite (p : Prop) [Decidable p] (a b : WG.M α) :
    (liftWGPrefix (if p then a else b) : WGPrefix E α) =
      if p then liftWGPrefix a else liftWGPrefix b := by
  split <;> rfl

theorem nonce_staging_specialization (pid : PeerId) :
    stagingObserved nonceHooks pid = Nonce.stagingObserved pid := by
  unfold stagingObserved Nonce.stagingObserved
  simp only [noKey_lift nonceHooks rfl]
  dsimp only [nonceHooks]
  unfold HandshakeSecurity.Responder.selectionPrefix
  simp only [lift_bind,lift_pure,lift_ite,bind_assoc,Queues.RxCredits.bind_if_source,pure_bind]
  all_goals rfl

theorem nonce_staging_function : stagingObserved nonceHooks = Nonce.stagingObserved :=
  funext nonce_staging_specialization

theorem nonce_keepaliveObserved_eq : keepaliveObserved nonceHooks = Nonce.keepaliveObserved := by
  funext pid
  rw [keepalive_native nonceHooks rfl]
  unfold keepaliveInline Nonce.keepaliveObserved
  simp only [nonce_staging_function]
  all_goals rfl

theorem nonce_transmitObserved_eq : transmitObserved nonceHooks = Nonce.transmitObserved := by
  unfold transmitObserved Nonce.transmitObserved
  simp only [nonce_staging_function]
  all_goals rfl

theorem nonce_expiredKeepaliveObserved_eq : expiredKeepaliveObserved nonceHooks = Nonce.expiredKeepaliveObserved := by
  funext pid
  rw [expiredKeepalive_lift nonceHooks rfl]
  unfold Nonce.expiredKeepaliveObserved
  simp only [nonce_keepaliveObserved_eq]
  all_goals rfl

theorem nonce_persistentObserved_eq : persistentObserved nonceHooks = Nonce.persistentObserved := by
  unfold persistentObserved Nonce.persistentObserved
  simp only [nonce_keepaliveObserved_eq]
  all_goals rfl

theorem nonce_timerObserved_eq : timerObserved nonceHooks = Nonce.timerObserved := by
  funext pid t
  cases t with
  | retransmitHandshake => exact timer_retransmit_lift nonceHooks rfl pid
  | sendKeepalive => exact congrFun nonce_expiredKeepaliveObserved_eq pid
  | newHandshake => exact timer_new_lift nonceHooks rfl pid
  | zeroKeyMaterial => rfl
  | persistentKeepalive => exact congrFun nonce_persistentObserved_eq pid

theorem nonce_handshakeOps_eq : handshakeOps nonceHooks = Nonce.Handshake.ops := by
  unfold handshakeOps Nonce.Handshake.ops
  simp only [nonce_keepaliveObserved_eq]
  all_goals rfl

theorem nonce_handshakeObserved_eq : handshakeObserved nonceHooks = Nonce.Handshake.observed := by
  change Origins.HandshakeSources.stepWith (handshakeOps nonceHooks) = Nonce.Handshake.observed
  unfold Nonce.Handshake.observed
  simp only [nonce_handshakeOps_eq]
  all_goals rfl

theorem nonce_receiveTailObserved_eq : receiveTailObserved nonceHooks = Nonce.receiveTailObserved := by
  unfold receiveTailObserved Nonce.receiveTailObserved
  simp only [nonce_staging_function,prepare_lift nonceHooks rfl]
  all_goals rfl

theorem nonce_consumeObserved_eq : consumeObserved nonceHooks = Nonce.consumeObserved := by
  unfold consumeObserved Nonce.consumeObserved
  simp only [nonce_receiveTailObserved_eq]
  all_goals rfl

private theorem nonce_enter_neutral : nonceHooks.candidateEnter = (fun _ _ => pure 0) := rfl
private theorem nonce_leave_neutral : nonceHooks.candidateLeave = (fun _ => pure ()) := rfl

theorem nonce_pollObserved_eq : pollObserved nonceHooks = Nonce.pollObserved := by
  funext pid budget cb
  unfold pollObserved Nonce.pollObserved
  rw [nonce_enter_neutral,nonce_leave_neutral,AuthenticatedEffects.CandidatePoll.neutral]
  rw [nonce_consumeObserved_eq]
  exact AuthenticatedEffects.IndexedPoll.unindexed _ _ _ _ _ pid budget

theorem nonce_stackObserved_eq : stackObserved nonceHooks = Nonce.stackObserved := by
  unfold stackObserved Nonce.stackObserved
  simp only [nonce_transmitObserved_eq]
  all_goals rfl

theorem nonce_stackFlushObserved_eq : stackFlushObserved nonceHooks = Nonce.stackFlushObserved := by
  unfold stackFlushObserved Nonce.stackFlushObserved
  simp only [nonce_stackObserved_eq]
  all_goals rfl

theorem nonce_nativePollObserved_eq : nativePollObserved nonceHooks = Nonce.nativePollObserved := by
  funext pid budget
  rw [nativePoll_neutral _ rfl]
  unfold Nonce.nativePollObserved
  simp only [nonce_pollObserved_eq, nonce_stackFlushObserved_eq]
  all_goals rfl

theorem nonce_softirqObserved_eq : softirqObserved nonceHooks = Nonce.softirqObserved := by
  unfold softirqObserved Nonce.softirqObserved
  simp only [nonce_nativePollObserved_eq]
  all_goals rfl

theorem nonce_inlinePollObserved_eq : inlinePollObserved nonceHooks = Nonce.inlinePollObserved := by
  unfold inlinePollObserved Nonce.inlinePollObserved
  simp only [nonce_nativePollObserved_eq]
  all_goals rfl

theorem nonce_irqExitObserved_eq : irqExitObserved nonceHooks = Nonce.irqExitObserved := by
  unfold irqExitObserved Nonce.irqExitObserved
  simp only [nonce_softirqObserved_eq]
  all_goals rfl

theorem nonce_reschedObserved_eq : (@reschedObserved Nonce.Allocation) = Nonce.reschedObserved := by
  unfold reschedObserved Nonce.reschedObserved
  all_goals rfl

theorem nonce_encryptTailObserved_eq : encryptTailObserved nonceHooks = Nonce.encryptTailObserved := by
  unfold encryptTailObserved Nonce.encryptTailObserved
  simp only [nonce_reschedObserved_eq]
  all_goals rfl

theorem nonce_encryptIterObserved_eq : encryptIterObserved nonceHooks = Nonce.encryptIterObserved := by
  unfold encryptIterObserved Nonce.encryptIterObserved
  simp only [nonce_softirqObserved_eq, nonce_encryptTailObserved_eq]
  all_goals rfl

theorem nonce_txIterObserved_eq : txIterObserved nonceHooks = Nonce.txIterObserved := by
  unfold txIterObserved Nonce.txIterObserved
  simp only [nonce_reschedObserved_eq]
  all_goals rfl

theorem nonce_decryptStepObserved_eq : decryptStepObserved nonceHooks = Nonce.decryptStepObserved := by
  unfold decryptStepObserved Nonce.decryptStepObserved
  simp only [nonce_softirqObserved_eq, nonce_irqExitObserved_eq]
  all_goals rfl

theorem nonce_decryptIterObserved_eq : decryptIterObserved nonceHooks = Nonce.decryptIterObserved := by
  unfold decryptIterObserved Nonce.decryptIterObserved
  simp only [nonce_reschedObserved_eq, nonce_decryptStepObserved_eq]
  all_goals rfl

theorem nonce_receiveIterObserved_eq : receiveIterObserved nonceHooks = Nonce.receiveIterObserved := by
  unfold receiveIterObserved Nonce.receiveIterObserved
  simp only [nonce_handshakeObserved_eq]
  all_goals rfl

theorem nonce_cryptAheadObserved_eq : cryptAheadObserved nonceHooks = Nonce.cryptAheadObserved := by
  unfold cryptAheadObserved Nonce.cryptAheadObserved
  simp only [nonce_encryptIterObserved_eq]
  all_goals rfl

theorem nonce_iterationObserved_eq : iterationObserved nonceHooks = Nonce.iterationObserved := by
  unfold iterationObserved Nonce.iterationObserved
  simp only [nonce_encryptIterObserved_eq, nonce_txIterObserved_eq, nonce_decryptIterObserved_eq, nonce_receiveIterObserved_eq, nonce_cryptAheadObserved_eq]
  all_goals rfl

theorem nonce_scheduleObserved_eq : scheduleObserved nonceHooks = @Nonce.scheduleObserved := by
  unfold scheduleObserved Nonce.scheduleObserved
  simp only [nonce_softirqObserved_eq, nonce_iterationObserved_eq]
  all_goals rfl

theorem nonce_cryptObserved_eq : cryptObserved nonceHooks = Nonce.cryptObserved := by
  unfold cryptObserved Nonce.cryptObserved
  simp only [nonce_scheduleObserved_eq]
  all_goals rfl

theorem nonce_sendWorkersObserved_eq : sendWorkersObserved nonceHooks = Nonce.sendWorkersObserved := by
  unfold sendWorkersObserved Nonce.sendWorkersObserved
  simp only [nonce_scheduleObserved_eq, sendWorker_lift nonceHooks rfl]
  all_goals rfl

theorem nonce_afterXmitObserved_eq : afterXmitObserved nonceHooks = Nonce.afterXmitObserved := by
  unfold afterXmitObserved Nonce.afterXmitObserved
  simp only [nonce_cryptObserved_eq, nonce_sendWorkersObserved_eq]
  all_goals rfl

theorem nonce_timerSectionObserved_eq : (@timerSectionObserved Nonce.Allocation) = Nonce.timerSectionObserved := by
  unfold timerSectionObserved Nonce.timerSectionObserved
  all_goals rfl

private theorem timer_selected_neutral (d : Device) (j : UInt64) (pid : PeerId)
    (t : PeerTimer) (we : WheelEntry) :
    nonceHooks.timerSelected d j pid t we = pure 0 := rfl

private theorem timer_finished_neutral (token : Nat) :
    nonceHooks.timerFinished token = pure () := rfl

theorem nonce_timersObserved_eq : timersObserved nonceHooks = Nonce.timersObserved := by
  unfold timersObserved Nonce.timersObserved
  simp only [nonce_timerObserved_eq, nonce_cryptObserved_eq, nonce_timerSectionObserved_eq,timer_selected_neutral,timer_finished_neutral,pure_bind,sendWorker_lift nonceHooks rfl]
  all_goals rfl

theorem nonce_placeholderTimersObserved_eq : placeholderTimersObserved nonceHooks = Nonce.placeholderTimersObserved := by
  unfold placeholderTimersObserved Nonce.placeholderTimersObserved
  simp only [nonce_timerObserved_eq, nonce_cryptObserved_eq, nonce_sendWorkersObserved_eq, nonce_timerSectionObserved_eq,timer_selected_neutral,timer_finished_neutral,pure_bind]
  all_goals rfl

theorem nonce_idleTimersObserved_eq : idleTimersObserved nonceHooks = Nonce.idleTimersObserved := by
  unfold idleTimersObserved Nonce.idleTimersObserved
  simp only [nonce_timersObserved_eq, nonce_placeholderTimersObserved_eq]
  all_goals rfl

theorem nonce_afterAdvanceObserved_eq : afterAdvanceObserved nonceHooks = Nonce.afterAdvanceObserved := by
  unfold afterAdvanceObserved Nonce.afterAdvanceObserved
  simp only [nonce_timersObserved_eq, nonce_placeholderTimersObserved_eq]
  all_goals rfl

theorem nonce_receiveEntryObserved_eq : (@receiveEntryObserved Nonce.Allocation) = Nonce.receiveEntryObserved := by
  unfold receiveEntryObserved Nonce.receiveEntryObserved
  all_goals rfl

theorem nonce_multicastObserved_eq : (@multicastObserved Nonce.Allocation) = Nonce.multicastObserved := by
  unfold multicastObserved Nonce.multicastObserved
  all_goals rfl

theorem nonce_drainObserved_eq : (@drainObserved Nonce.Allocation) = Nonce.drainObserved := by
  unfold drainObserved Nonce.drainObserved
  all_goals rfl

theorem nonce_injectObserved_eq : injectObserved nonceHooks = Nonce.injectObserved := by
  unfold injectObserved Nonce.injectObserved
  simp only [nonce_cryptObserved_eq, nonce_receiveEntryObserved_eq, nonce_drainObserved_eq]
  all_goals rfl

theorem nonce_afterBatchObserved_eq : afterBatchObserved nonceHooks = Nonce.afterBatchObserved := by
  unfold afterBatchObserved Nonce.afterBatchObserved
  simp only [nonce_scheduleObserved_eq, nonce_cryptObserved_eq, nonce_sendWorkersObserved_eq, nonce_drainObserved_eq, sendWorker_lift nonceHooks rfl]
  all_goals rfl

theorem nonce_floodObserved_eq : floodObserved nonceHooks = Nonce.floodObserved := by
  unfold floodObserved Nonce.floodObserved
  simp only [nonce_inlinePollObserved_eq, nonce_receiveEntryObserved_eq, nonce_drainObserved_eq, nonce_afterBatchObserved_eq]
  all_goals rfl

private theorem nonce_fixture_neutral :
    fixtureOps nonceHooks = AuthenticatedEffects.FixtureEffects.neutral := rfl

theorem nonce_batchItemObserved_eq : batchItemObserved nonceHooks = Nonce.batchItemObserved := by
  unfold batchItemObserved Nonce.batchItemObserved
  simp only [nonce_fixture_neutral, AuthenticatedEffects.FixtureEffects.run_neutral, nonce_transmitObserved_eq, nonce_inlinePollObserved_eq, nonce_receiveEntryObserved_eq, nonce_multicastObserved_eq]
  all_goals rfl

theorem nonce_batchObserved_eq : batchObserved nonceHooks = Nonce.batchObserved := by
  unfold batchObserved Nonce.batchObserved
  simp only [nonce_afterBatchObserved_eq, nonce_batchItemObserved_eq]
  all_goals rfl

theorem nonce_syscallXmitObserved_eq : syscallXmitObserved nonceHooks = Nonce.syscallXmitObserved := by
  unfold syscallXmitObserved Nonce.syscallXmitObserved
  simp only [nonce_fixture_neutral, AuthenticatedEffects.FixtureEffects.run_neutral, nonce_transmitObserved_eq, nonce_multicastObserved_eq]
  all_goals rfl

theorem nonce_configOut_eq : (@configOut Nonce.Allocation) = Nonce.configOut := by
  unfold configOut Nonce.configOut
  all_goals rfl

theorem nonce_configTailFinish_eq : configTailFinish nonceHooks = Nonce.configTailFinish := by
  unfold configTailFinish Nonce.configTailFinish
  simp only [nonce_fixture_neutral, AuthenticatedEffects.FixtureEffects.peerFinish_neutral, nonce_staging_function, nonce_keepaliveObserved_eq, nonce_configOut_eq]
  unfold AuthenticatedEffects.FixtureEffects.peerFinishWith
  all_goals rfl

theorem nonce_configTail_eq : configTail nonceHooks = Nonce.configTail := by
  unfold configTail Nonce.configTail
  simp only [nonce_configOut_eq, nonce_configTailFinish_eq]
  all_goals rfl

theorem nonce_configUpdate_eq : configUpdate nonceHooks = Nonce.configUpdate := by
  unfold configUpdate Nonce.configUpdate
  simp only [nonce_configOut_eq, nonce_configTail_eq, remove_lift nonceHooks rfl]
  all_goals rfl

theorem nonce_configPeer_eq : configPeer nonceHooks = Nonce.configPeer := by
  unfold configPeer Nonce.configPeer
  simp only [nonce_configOut_eq, nonce_configUpdate_eq]
  all_goals rfl

theorem nonce_configPeers_eq : configPeers nonceHooks = Nonce.configPeers := by
  unfold configPeers Nonce.configPeers
  simp only [nonce_configPeer_eq]
  all_goals rfl

private theorem nonce_remove_function : removeObserved nonceHooks = fun peer => liftWGPrefix (peerRemove peer) :=
  funext (remove_lift nonceHooks rfl)

theorem nonce_configKey_eq : configKey nonceHooks = Nonce.configKey := by
  unfold configKey Nonce.configKey
  simp only [nonce_fixture_neutral, AuthenticatedEffects.FixtureEffects.run_neutral, nonce_staging_function, nonce_configPeers_eq, nonce_remove_function]
  all_goals rfl

theorem nonce_configDeviceUpdate_eq : configDeviceUpdate nonceHooks = Nonce.configDeviceUpdate := by
  unfold configDeviceUpdate Nonce.configDeviceUpdate
  simp only [nonce_configKey_eq, removeAll_lift nonceHooks rfl]
  all_goals rfl

theorem nonce_configDevice_eq : configDevice nonceHooks = Nonce.configDevice := by
  unfold configDevice Nonce.configDevice
  simp only [nonce_configDeviceUpdate_eq]
  all_goals rfl

theorem nonce_openObserved_eq : openObserved nonceHooks = Nonce.openObserved := by
  unfold openObserved Nonce.openObserved
  simp only [nonce_fixture_neutral, AuthenticatedEffects.FixtureEffects.open_neutral, nonce_staging_function, nonce_keepaliveObserved_eq]
  unfold AuthenticatedEffects.FixtureEffects.openWith
  all_goals rfl

theorem nonce_upObserved_eq : upObserved nonceHooks = Nonce.upObserved := by
  unfold upObserved Nonce.upObserved
  simp only [nonce_openObserved_eq]
  all_goals rfl

theorem nonce_envUpObserved_eq : envUpObserved nonceHooks = Nonce.envUpObserved := by
  unfold envUpObserved Nonce.envUpObserved
  simp only [nonce_upObserved_eq]
  all_goals rfl

theorem nonce_retainedObserved_eq : retainedObserved nonceHooks = Nonce.retainedObserved := by
  funext call
  cases call <;> unfold retainedObserved Nonce.retainedObserved
  case wgUp => rw [nonce_envUpObserved_eq]
  case wgDown =>
    rw [envDown_lift nonceHooks rfl,socketCall_lift]
    rfl
  all_goals rfl

theorem nonce_observeObserved_eq : observeObserved nonceHooks = Nonce.observeObserved := by
  unfold observeObserved Nonce.observeObserved
  simp only [nonce_idleTimersObserved_eq]
  change (_ >>= fun _ => AuthenticatedEffects.DeliverySource.observeWith (liftPrefix Env.deliverSent)) = _
  rw [AuthenticatedEffects.DeliverySource.observe_native]

theorem nonce_dispatchObserveObserved_eq : dispatchObserveObserved nonceHooks = Nonce.dispatchObserveObserved := by
  unfold dispatchObserveObserved Nonce.dispatchObserveObserved
  simp only [nonce_observeObserved_eq]
  all_goals rfl

theorem nonce_dispatchSetObserved_eq : dispatchSetObserved nonceHooks = Nonce.dispatchSetObserved := by
  unfold dispatchSetObserved Nonce.dispatchSetObserved
  simp only [nonce_configDevice_eq]
  all_goals rfl

theorem nonce_dispatchCreateObserved_eq : (@dispatchCreateObserved Nonce.Allocation) = Nonce.dispatchCreateObserved := by
  unfold dispatchCreateObserved Nonce.dispatchCreateObserved
  all_goals rfl

theorem nonce_dispatchDeleteObserved_eq : dispatchDeleteObserved nonceHooks = Nonce.dispatchDeleteObserved := by
  unfold dispatchDeleteObserved Nonce.dispatchDeleteObserved
  rw [envDelete_lift nonceHooks rfl]

theorem nonce_dispatchObserved_eq : dispatchObserved nonceHooks = Nonce.dispatchObserved := by
  unfold dispatchObserved Nonce.dispatchObserved
  simp only [nonce_injectObserved_eq, nonce_floodObserved_eq, nonce_batchObserved_eq, nonce_syscallXmitObserved_eq, nonce_retainedObserved_eq, nonce_dispatchObserveObserved_eq, nonce_dispatchSetObserved_eq, nonce_dispatchCreateObserved_eq, nonce_dispatchDeleteObserved_eq]
  all_goals rfl

theorem nonce_syscallObserved_eq : syscallObserved nonceHooks = Nonce.syscallObserved := by
  unfold syscallObserved Nonce.syscallObserved
  simp only [nonce_sendWorkersObserved_eq, nonce_afterXmitObserved_eq, nonce_idleTimersObserved_eq, nonce_afterAdvanceObserved_eq, nonce_dispatchObserved_eq]
  all_goals rfl

theorem nonce_executeObserved_eq : executeObserved nonceHooks = Nonce.executeObserved := by
  unfold executeObserved Nonce.executeObserved
  simp only [nonce_syscallObserved_eq]
  all_goals rfl

/-- The selected native prefix retains the exact initialized reservation
execution and its internal history. -/
theorem nonce_specialization (trace : Runner.Trace) (placeholders : Bool) :
    executeObserved nonceHooks trace placeholders = Nonce.executeObserved trace placeholders := by
  rw [nonce_executeObserved_eq]

end Leanux.Proofs.WG.TransmitSecurity.Driver
