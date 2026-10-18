import Leanux.Proofs.WG.Index.TxCompletionCoreSource
import Leanux.Proofs.WG.Index.TxCutsSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem txStep_core (cs : Ledger) (loans : Reservations) (history : List SessionOrigin.Receipt)
    (pid : PeerId) (w v : WGWorld) (a b : Ambient) (result : Bool)
    (entry : DeviceBoundary.Entry cs loans w ∧ Reached.Core w)
    (current : CurrentLifecycle.Inv history w)
    (run : ((txStep pid).run w).run a=.ok ((result,v),b)) : Reached.Core v := by
  rcases tx_step_cut pid w v a b result run with idle | active
  · exact ConfigurationIndex.fields_core w v idle.2 entry.2
  · obtain ⟨first,tail,d,p,q,head,start,middle,completed,device,resident,sameQueue,queueEq,completion,dispose⟩ := active
    obtain ⟨holders,funded,stable⟩ := entry.1.1
    have queue : handoffTxView w pid=some p.txQueue.all := by simp [handoffTxView,device,resident]
    have headEq : p.txQueue.all.head?=some (first::tail) := by rw [queueEq]; rfl
    obtain ⟨chosen,remaining,selected,_,_⟩ := funded.tx_selected queue headEq
    let cachedDevice := {d with peers:=d.peers.insert pid {p with txQueue:=q}}
    let cached : WGWorld := {w with dev:=some cachedDevice}
    have cachedResident : cachedDevice.peers[pid]?=some {p with txQueue:=q} := by simp [cachedDevice]
    have cachedEntry : DeviceBoundary.Entry cs loans cached ∧ Reached.Core cached :=
      peek_boundary cs loans w d pid p q device resident sameQueue entry
    have cachedCurrent : CurrentLifecycle.Inv history cached :=
      queue_current history w d pid p q device resident current
    have cachedAccount := (pinned_const _private.Leanux.Proofs.WG.Queues.TxHolderStep.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.peek_install)
      funded stable device resident q sameQueue
    have dropEq : q.dropPeeked.all=q.all.tail := by rw [sameQueue,queueEq]; rfl
    have dropped := selected_drop_boundary cs loans holders chosen remaining cached cachedDevice pid
      {p with txQueue:=q} q.dropPeeked rfl cachedResident cachedEntry
      cachedAccount.1 cachedAccount.2 selected dropEq
    let droppedWorld : WGWorld :=
      {cached with dev:=some {cachedDevice with peers:=cachedDevice.peers.insert pid {p with txQueue:=q.dropPeeked}}}
    have droppedEntry : DeviceBoundary.Entry cs (chosen.owner::loans) droppedWorld ∧ Reached.Core droppedWorld :=
      ⟨⟨⟨holders.withoutTx remaining,dropped.1,dropped.2.1⟩,dropped.2.2.1,dropped.2.2.2.1⟩,
        dropped.2.2.2.2⟩
    have droppedCurrent : CurrentLifecycle.Inv history droppedWorld :=
      queue_current history cached cachedDevice pid {p with txQueue:=q} q.dropPeeked
        rfl cachedResident cachedCurrent
    have completedEntry : DeviceBoundary.Entry cs (chosen.owner::loans) completed ∧ Reached.Core completed := by
      cases condition : (head.state == PacketState.crypted) with
      | false =>
        simp only [condition,Bool.false_eq_true,ite_false] at completion
        cases completion
        exact droppedEntry
      | true =>
        simp only [condition,ite_true] at completion
        exact completion_boundary cs (chosen.owner::loans) history pid (first::tail)
          droppedWorld completed start middle droppedEntry droppedCurrent completion
    have result := (hoare_iff_run_ambient _ _ _).mp
      (dispose_boundary cs chosen.owner loans (first::tail) head.keypair)
      completed middle result v b completedEntry (selected.slot ▸ dispose)
    exact result.2

theorem txIteration_core (cs : Ledger) (loans : Reservations) (history : List SessionOrigin.Receipt)
    (pid : PeerId) :
    Hoare (txIter pid (Env.condResched .txWorker))
      (fun w : World => (DeviceBoundary.Entry cs loans w.wg ∧ Reached.Core w.wg) ∧ CurrentLifecycle.Inv history w.wg)
      (fun _ w => Reached.Core w.wg) := by
  have step : Hoare (liftWG (txStep pid))
      (fun w : World => (DeviceBoundary.Entry cs loans w.wg ∧ Reached.Core w.wg) ∧ CurrentLifecycle.Inv history w.wg)
      (fun _ w => Reached.Core w.wg) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v pre run
    rw [liftWG_run] at run
    cases native : ((txStep pid).run w.wg).run w.ambient with
    | error stop => simp [native,Except.map] at run
    | ok out =>
      rcases out with ⟨⟨value,final⟩,after⟩
      simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      exact txStep_core cs loans history pid w.wg final w.ambient after value pre.1 pre.2 native
  have need : Preserves (fun w : World=>Reached.Core w.wg) (Env.condResched .txWorker) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v pre run
    have frame := (ProjectedAction.iff_run _ _ _).mp (condResched_sameKernel .txWorker) w result v run
    exact Reached.core_device (congrArg (fun s : ProductStore43=>s.2.2.2.dev) frame) pre
  unfold txIter workerIter
  apply hoare_bind _ _ step
  intro more
  cases more with
  | false => exact preserves_pure IterResult.ended
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false,bind_assoc]
    apply preserves_bind need
    intro yielded
    apply preserves_bind (productAmbient_spec (AmbientM.branch .txNeedResched yielded)
      (fun w : World=>Reached.Core w.wg) (fun _ _ pre=>pre))
    intro choice
    exact preserves_pure (if choice then IterResult.yielded else IterResult.continued)

theorem tx_observed (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) := by
  apply Reached.aux_pair _ initial loans before (HolderAuxScheduler.tx_preserves initial loans before pid)
  intro w h entry result v run
  have native := ((RxHistory.mixed_erases
    (txIterPrefix_erases pid (erasesPrefix_lift (Env.condResched .txWorker))) w h).symm.trans run)
  obtain ⟨suffix,_,boundary⟩ := entry.1.1.1
  have core := (hoare_iff_run _ _ _).mp
    (txIteration_core (remaining initial (NapiCarrier.removedPackets suffix)) loans
      (Origins.HistorySupport.sessions h) pid) w result v
    ⟨⟨⟨boundary,entry.2.1,HolderAuxiliary.owner_configured entry.1.2.1⟩,entry.2.2⟩,
      entry.1.2.1.current.2.1⟩ native
  have needFrame : SameView (fun w : World=>BaseCoherence.view w.wg) (Env.condResched .txWorker) :=
    (condResched_sameKernel .txWorker).of_factor
      (fun s : ProductStore43=>BaseCoherence.view {dev:=s.2.2.2.dev})
      (fun w : World=>BaseCoherence.view w.wg) (fun _=>rfl)
  have base := (ProjectedAction.iff_run _ _ _).mp
    (BaseCoherence.txIter_view pid (Env.condResched .txWorker) needFrame) w result v native
  exact ⟨BaseCoherence.transport entry.2.1 base,core⟩

end Leanux.Proofs.WG.Index.CryptCore
