import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketEnvironmentSource
import Leanux.Proofs.WG.RetirementSecurity.TxWorkLifecycle

/-! Shutdown and the routing notifications carry the actual complete ledger
and native destructor prerequisites on the same execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet.Environment
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits Queues.RxCredits.DurableHolders TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
set_option maxHeartbeats 600000

def Ready (h : List Event) (w : World) : Prop :=
  CompleteProduct.Carrier h w ∧ Packet.NativeEntry w.wg

theorem native_store (same : wgStoreView v=wgStoreView w)
    (before : Packet.NativeEntry w) : Packet.NativeEntry v := by
  obtain ⟨⟨holders,account⟩,c7,c8⟩ := before.clear
  refine ⟨⟨⟨holders,account.store same⟩,?_,?_⟩,?_,TxWork.serving_store_transport same before.service⟩
  · exact (congrArg (fun s : WGStoreView=>activeCursor s.nlSock7) same).trans c7
  · exact (congrArg (fun s : WGStoreView=>activeCursor s.nlSock8) same).trans c8
  · change PeerReference.Positive (PeerReference.view v)
    rw [show PeerReference.view v=PeerReference.view w from
      congrArg (fun s : WGStoreView=>fun pid : PeerId=>(s.dev.bind fun d=>d.peers[pid]?).map Peer.refcount) same]
    exact before.positive

theorem quiet (action : Leanux.M α) (frame : SameProductStore action) :
    PrefixPreserves Ready CompleteProduct.Safe (liftPrefix action) := by
  apply PrefixEnsures.lift _ (fun h w before=>CompleteProduct.carrier_safe h w before.1)
  intro h w value v before run
  have same := congrArg (fun s : ProductStore43=>s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w value v run)
  exact ⟨CompleteProduct.store_transport h w v same before.1,native_store same before.2⟩

theorem down_checked : PrefixPreserves Ready CompleteProduct.Safe
    (liftWGObserver (Driver.downObserved hooks)) := by
  have packet := CompleteProduct.state (CompleteProduct.pair
    (CompleteLifecycle.down CompleteProduct.Safe CompleteProduct.account_safe)
    CompleteNative.down_erases CompleteNative.down)
  intro w h before
  obtain ⟨suffix,extended,safe,kept⟩ := packet w h before.1
  refine ⟨suffix,extended,safe,?_⟩
  cases performed : (runPrefix (liftWGObserver (Driver.downObserved hooks)) w h).1 with
  | error reason => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    rw [performed] at kept
    have native := (liftWGObserver_erases CompleteNative.down_erases w h).symm.trans performed
    have run := HolderPoll.native_receipt native
    exact ⟨kept,
      (hoare_iff_run_ambient _ _ _).mp Lifecycle.down_clear w.wg w.ambient value v.wg v.ambient before.2.clear run,
      (hoare_iff_run_ambient _ _ _).mp Lifecycle.positive_down w.wg w.ambient value v.wg v.ambient before.2.positive run,
      (hoare_iff_run_ambient _ _ _).mp TxWork.serving_down w.wg w.ambient value v.wg v.ambient before.2.service run⟩

private theorem routing_store (action : Net.M α) :
    SameProductStore (monadLift action : Leanux.M α) :=
  fun initial=>productRouting_spec action (·=initial)

theorem notify_down_store : SameProductStore notifyDown := by
  unfold notifyDown
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyDown
  unfold modifyRouting
  exact (routing_store _).bind (fun _=>(routing_store _).bind (fun _=>routing_store _))

theorem notify_unregister_store : SameProductStore notifyUnregister := by
  unfold notifyUnregister
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyUnregister
  unfold modifyRouting
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store).bind
    (fun _=>(routing_store _).bind (fun _=>routing_store _))

/-- Every counted shutdown successor is retained; the native notifications
preserve that same successor and the reference/service prerequisites. -/
theorem prefix_checked : PrefixPreserves Ready CompleteProduct.Safe prefixObserved := by
  have read := quiet (liftWG getDev) (liftWG_sameProductStore _ getDev_sameWGStore)
  have cut := quiet (skipCut allocCuts) (fun initial=>productAmbient_spec _ (fun w=>productStoreView w=initial) (fun _ _ before=>before))
  have sleep := quiet (liftWG mayHaveSlept) (liftWG_sameProductStore _ mayHaveSlept_sameWGStore)
  unfold prefixObserved
  apply PrefixPreserves.bind read
  intro d
  split
  · exact PrefixPreserves.bind down_checked (fun _=>
      PrefixPreserves.bind (quiet _ notify_down_store) (fun _=>
        PrefixPreserves.bind cut (fun _=>PrefixPreserves.bind (quiet _ notify_unregister_store) (fun _=>sleep))))
  · exact PrefixPreserves.bind cut (fun _=>PrefixPreserves.bind (quiet _ notify_unregister_store) (fun _=>sleep))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet.Environment
