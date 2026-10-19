import Leanux.Proofs.WG.RetirementSecurity.TxCoverageLifecycle

/-! Device creation starts with empty peer queues. Guarded deletion drops
all batch state at the actual empty-local outer boundary. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCovered.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits Native TxCovered.Configuration

private theorem drop : Preserves (Inv [] []) (modify (fun w : WGWorld => {w with dev := none}) : WG.M Unit) := by
  apply join
    (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OccurrenceLifecycle.«0».Leanux.Proofs.WG.RetirementSecurity.OccurrenceLifecycle.drop)
  apply hoare_modify
  intro w _ id packet found
  simp [TxDisposition.txPackets] at found

private theorem limiter : Preserves (Inv locals active) ratelimiterUninit := by
  apply join
    (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OccurrenceLifecycle.«0».Leanux.Proofs.WG.RetirementSecurity.OccurrenceLifecycle.limiter)
  apply TxCoverageNative.wire
  · exact ratelimiterUninit_sameRatelimiter.of_factor (fun s => handoffTxView {dev:=s.dev}) _ (fun _=>rfl)
  · exact ratelimiterUninit_sameRatelimiter.of_factor (fun s => txCryptWire {dev:=s.dev}) _ (fun _=>rfl)

theorem destruct : Preserves (Inv [] []) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact socket_reinit _ _)
    | (rx_retention_head peerRemoveAll; exact Removal.remove_all)
    | (rx_retention_head mayHaveSlept; exact coherent_store mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact limiter)
    | (rx_retention_head modify; exact drop)
    | (rx_retention_head retireDeviceUnits; exact coherent_store retireDeviceUnits_sameWGStore)
    | tx_covered_config_step

theorem delete (onDown onUnregister : WG.M Unit)
    (downRule : Preserves (Inv [] []) onDown) (unregisterRule : Preserves (Inv [] []) onUnregister) :
    Preserves (Inv [] []) (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact downRule
    | exact unregisterRule
    | (rx_retention_head wgDown; exact down)
    | (rx_retention_head wgDestruct; exact destruct)
    | (rx_retention_head mayHaveSlept; exact coherent_store mayHaveSlept_sameWGStore)
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
    | tx_covered_config_step

theorem delete_default : Preserves (Inv [] []) (wgDelete : WG.M Int) :=
  delete _ _ (preserves_pure ()) (preserves_pure ())


theorem create : Preserves (Inv [] []) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  refine ⟨(hoare_iff_run_ambient _ _ _).mp OccurrenceLifecycle.create w a result v b before.1 run,?_⟩
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,new⟩
  · have fields : txCryptWire v = txCryptWire w := by
      simpa only [linkView,linkStore,linkDevice,wgStoreView,txCryptWire,TxRing.nativeCell,
        TxDisposition.txPackets,Option.map_map,Option.bind_map,Function.comp_def] using
        congrArg (fun s : WGStoreView => txCryptWire {dev:=s.dev}) same
    have queues : txQueueContents v = txQueueContents w := by
      funext pid
      simpa only [linkView,linkStore,linkDevice,wgStoreView,txQueueContents,handoffTxView,
        Option.bind_map,Function.comp_def] using
        congrArg (fun s : WGStoreView => txQueueContents {dev:=s.dev} pid) same
    exact before.2.cells (congrArg Prod.snd fields) queues
  · intro id packet found
    obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp found
    have cells : d.txSkbs = {} := by
      simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
        device,Option.map_some,Option.map_map,Function.comp_def,Option.some.injEq] using
        congrArg (fun s : WGStoreView => s.dev.map Device.txSkbs) new
    simp [cells] at stored

end Leanux.Proofs.WG.RetirementSecurity.TxCovered.Lifecycle
