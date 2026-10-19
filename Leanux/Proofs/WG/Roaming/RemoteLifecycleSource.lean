import Leanux.Proofs.WG.Index.LifecycleDeleteRuleSource
import Leanux.Proofs.WG.Roaming.RemoteLifecycleFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming.RemoteLifecycle
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open RemoteSilent

theorem dumpContracts (entry : RemoteMap) : Config.DumpInvariant.Contracts (Retained entry) where
  stable := by
    intro w v same pre
    have endpoints := congrArg (fun s => responseEndpointMap s.dev) same
    have remotes := endpointMap_destinations endpoints
    change destinationAt v = destinationAt w at remotes
    simpa only [RemoteSilent.Retained,remotes] using pre
  acquire := fun pid => (ensures_iff _ _ _).mp (peerGet_retained entry pid)
  release := fun pid => (ensures_iff _ _ _).mp (peerPut_remotes pid entry)

theorem dump (entry : RemoteMap) (call : NetlinkDumpCall) :
    Preserves (Retained entry) call.original :=
  Config.DumpInvariant.call (dumpContracts entry) call

theorem open_native (entry : RemoteMap) : Preserves (Retained entry) wgOpen :=
  LifecycleSource.open_preserves _
    ((RemoteCompletion.store_remotes getDev_sameWGStore).wp (RemoteRetained entry))
    (fun pid => (RemoteSilent.getPeer_frame pid).wp (RemoteRetained entry))
    (fun port => (RemoteMaintenance.socket_frame (socketInit_sameSocket port)).wp (RemoteRetained entry))
    (fun pid => (ensures_iff _ _ _).mp (staging_remotes _ (Index.StagingRich.sendStagedPackets_rich pid) entry))
    (fun pid => (ensures_iff _ _ _).mp (staging_remotes _ (Index.StagingRich.sendKeepalive_rich pid) entry))

theorem up_native (entry : RemoteMap) : Preserves (Retained entry) WG.wgUp := by
  unfold WG.wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_native entry)
    | (rx_retention_head modifyDev; apply SameView.wp (P:=RemoteRetained entry); apply modifyDev_remotes; intro d; rfl)
    | rx_retention_step

theorem preexit_native (entry : RemoteMap) : Preserves (Retained entry) netnsPreExit :=
  LifecycleSource.preexit_preserves _
    (by apply (hoare_iff_run_ambient _ _ _).mpr; intro w a r v b pre run; cases run; exact pre)
    ((RemoteCompletion.store_remotes getDev_sameWGStore).wp (RemoteRetained entry))
    ((modifyDev_remotes (fun d=>{d with carrier:=false,creatingNet:=false}) (fun _=>rfl)).wp (RemoteRetained entry))
    ((RemoteMaintenance.socket_frame (socketReinit_sameSocket none none)).wp (RemoteRetained entry))
    (fun pid => (RemoteMutation.clear_source_destinations pid).wp (RemoteRetained entry))

theorem create_native (entry : RemoteMap) : Preserves (Retained entry) WG.wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g ambient result final after prior run
  have effect := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView g))
    g ambient result final after rfl run
  rcases effect with same | ⟨_,fresh⟩
  · have endpoints := congrArg (fun s : WGStoreView => responseEndpointMap s.dev) same
    rw [link_remotes,link_remotes] at endpoints
    have remotes := endpointMap_destinations endpoints
    simpa only [RemoteSilent.Retained,remotes] using prior
  · have endpoints := congrArg (fun s : WGStoreView => responseEndpointMap s.dev) fresh
    rw [link_remotes] at endpoints
    intro pid remote present
    have absent : responseEndpointMap final.dev pid = none := by
      rw [endpoints]
      simp [registeredLink,setupLink,responseEndpointMap,linkDevice]
    have absentRemote : destinationAt final pid = none := by
      cases device : final.dev with
      | none => simp [destinationAt,peerAt,device]
      | some d =>
        cases resident : d.peers[pid]? with
        | none => simp [destinationAt,peerAt,device,resident]
        | some p => simp [responseEndpointMap,device,resident] at absent
    rw [absentRemote] at present
    cases present

theorem lift_native {α : Type} (entry : RemoteMap) (action : WG.M α)
    (kept : Preserves (Retained entry) action) :
    Preserves (fun w : World => Retained entry w.wg) (liftWG action) :=
  PublicationPoll.native_product (Retained entry) action kept

theorem envUp_native (entry : RemoteMap) :
    Preserves (fun w : World => Retained entry w.wg) Env.wgUp :=
  LifecycleSource.envUp_preserves _
    (fun action same => RemoteWorkers.product_store entry action same)
    (lift_native entry _ (up_native entry))

theorem envDown_native (entry : RemoteMap) :
    Preserves (fun w : World => Retained entry w.wg) Env.wgDown :=
  LifecycleSource.envDown_preserves _
    (fun action same => RemoteWorkers.product_store entry action same)
    (lift_native entry _ ((ensures_iff _ _ _).mp (RemoteMaintenance.down entry)))
    (RemoteWorkers.product_store entry _ PendingScheduler.requireIdleDevice_store)

theorem cleanup_native (entry : RemoteMap) :
    Preserves (fun w : World => Retained entry w.wg) Env.netnsCleanup :=
  LifecycleSource.cleanup_preserves _
    (fun action same => RemoteWorkers.product_store entry action same)
    (lift_native entry _ (preexit_native entry))

theorem envDelete_native (entry : RemoteMap) :
    Preserves (fun w : World => Retained entry w.wg) Env.wgDelete :=
  LifecycleSource.envDelete_preserves _ (fun action same=>RemoteWorkers.product_store entry action same)
    (lift_native entry _ ((ensures_iff _ _ _).mp (RemoteMaintenance.down entry)))
    (lift_native entry _ ((ensures_iff _ _ _).mp (RemoteMaintenance.destruct entry)))

end Leanux.Proofs.WG.Roaming.RemoteLifecycle
