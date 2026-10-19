import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionCreate

/-! Native lifecycle transport at empty-local boundaries. These endpoint
invariants do not classify reset as a disposal: that separate claim uses the
actual before-reset no-residual theorem and its source-derived entry premises. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem no_peers (absent : ∀pid,peerAt w pid=none) : Obligations crypt tx w := by
  constructor
  · intro pid p found
    simp [absent] at found
  · intro pid p found
    simp [absent] at found

theorem serving_create : Preserves (Serving [] [] tx) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  refine ⟨?_,(hoare_iff_run_ambient _ _ _).mp TxCovered.Lifecycle.create w a result v b before.2 run⟩
  have endpoint:=(hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w)) w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have wire : txCryptWire v=txCryptWire w := by
      simpa only [linkView,linkStore,linkDevice,wgStoreView,txCryptWire,TxRing.nativeCell,
        TxDisposition.txPackets,Option.map_map,Option.bind_map,Function.comp_def] using
        congrArg (fun s:WGStoreView=>txCryptWire {dev:=s.dev}) same
    have contents : txQueueContents v=txQueueContents w := by
      funext pid
      simpa only [linkView,linkStore,linkDevice,wgStoreView,txQueueContents,handoffTxView,
        Option.bind_map,Function.comp_def] using
        congrArg (fun s:WGStoreView=>txQueueContents {dev:=s.dev} pid) same
    have work : queued v=queued w := by
      simpa only [linkView,linkStore,linkDevice,wgStoreView,queued,Option.map_map,Function.comp_def] using
        congrArg (fun s:WGStoreView=>queued {dev:=s.dev}) same
    exact before.1.contents contents (congrArg Prod.snd wire) (crypt_items_eq (congrArg Prod.fst wire)) work
  · apply no_peers
    intro pid
    cases device:v.dev with
    | none=>simp [peerAt,device]
    | some d=>
      have peers:d.peers={} := by
        simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
          device,Option.map_some,Option.map_map,Function.comp_def,Option.some.injEq] using
          congrArg (fun s:WGStoreView=>s.dev.map Device.peers) fresh
      simp [peerAt,device,peers]

theorem destruct_absent (run : (wgDestruct.run w).run a=.ok (((),v),b)) : v.dev=none := by
  rw [Destruct.factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,_,tail⟩:=run
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨_,s,e,reset,retired⟩:=tail
  cases reset
  have same:=(ProjectedAction.iff_run_ambient _ _ _).mp retireDeviceUnits_sameWGStore _ _ () v b retired
  exact congrArg WGStoreView.dev same

theorem serving_destruct : Preserves (Serving [] [] tx) wgDestruct := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  refine ⟨no_peers (fun pid=>?_),
    (hoare_iff_run_ambient _ _ _).mp TxCovered.Lifecycle.destruct w a () v b before.2 run⟩
  simp [peerAt,destruct_absent run]

theorem create_actor : Preserves (At (Covered [] []) [] active) (liftWG wgCreate) :=
  At.native (fun _=>serving_create) TxSuspension.device_create

theorem destruct_actor : Preserves (At (Covered [] []) [] active) (liftWG wgDestruct) :=
  At.native (fun _=>serving_destruct) TxSuspension.destruct

theorem initial_at (net bare : Bool) (w : World)
    (same : wgStoreView w.wg=wgStoreView (Runner.initialWG net bare)) : At (Covered [] []) [] [] w := by
  have service : Obligations [] (actors w.ambient.suspended) (Runner.initialWG net bare) :=
    no_peers (fun pid=>by cases net <;> cases bare <;> simp [peerAt,Runner.initialWG])
  have state : Serving [] [] (actors w.ambient.suspended) w.wg :=
    serving_store_transport same ⟨service,TxCovered.Lifecycle.initial net bare⟩
  simpa only [At,Serving,List.nil_append] using state

end Leanux.Proofs.WG.RetirementSecurity.TxWork
