import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeviceConfiguration
import Leanux.Proofs.Framing.WGDeviceLifecycle

/-! Native device controls and empty-boundary lifecycle transport. Device
creation/destruction occur outside suspended TX locals; all source guards and
allocation refusals remain present. This is state transport, not progress. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceLifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits OccurrenceStack OccurrenceHandshake OccurrenceConfiguration

theorem initial (net bare : Bool) : Ready [] [] (Runner.initialWG net bare) :=
  ⟨(StackOwnership.initial net bare).2.1,(StackOwnership.initial net bare).1.2⟩

theorem open_device : Preserves (Ready locals active) wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket_init _)
    | (rx_retention_head sendStagedPackets; exact staged _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Ready locals active)
       intro x b
       change Preserves (Ready locals active) _)
    | occurrence_config_step

theorem up : Preserves (Ready locals active) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_device)
    | occurrence_config_step

theorem stop : Preserves (Ready locals active) wgStop := by
  unfold wgStop requireNotPending
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact OccurrenceTimers.purge _)
    | (rx_retention_head timersStop; exact OccurrenceRemoval.timers_stop _)
    | (rx_retention_head handshakeClear
       exact RxPollOccurrences.join (KeyMaintenanceCall.erases (.clear _)) (KeyMaintenanceCall.allocation (.clear _))
         (occurrence_passive (OccurrenceKeys.handshake_clear_wire _) (OccurrenceKeys.handshake_clear_queues _)))
    | (rx_retention_head keypairsClear
       exact RxPollOccurrences.join (keypairsClearPrefix_erases _) (keypairsClearPrefix_allocation _)
         (occurrence_passive (OccurrenceKeys.clear_wire _) (OccurrenceKeys.clear_queues _)))
    | (rx_retention_head resetLastSentHandshake
       exact RxPollOccurrences.join (KeyMaintenanceCall.erases (.reset _)) (KeyMaintenanceCall.allocation (.reset _))
         (occurrences_queueContents (OccurrenceCreation.reset_wire _) (OccurrenceCreation.reset_contents _)))
    | (rx_retention_head socketReinit; exact socket_reinit _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Ready locals active)
       intro x b
       change Preserves (Ready locals active) _)
    | occurrence_config_step

theorem down : Preserves (Ready locals active) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop)
    | occurrence_config_step

theorem no_device (w : WGWorld) (none : w.dev = Option.none) : TxOccurrences [] [] w := by
  constructor
  · constructor <;> simp [txLocalItems,peerAt,none]
  · constructor
    · intro d device; simp [none] at device
    · simp [txCryptItems,none]
    · intro items member; simp [txCryptItems,none] at member
    · intro items member; simp [txCryptItems,none] at member

private theorem drop : Preserves (Ready [] []) (modify (fun w : WGWorld => {w with dev := none}) : WG.M Unit) := by
  apply RxPollOccurrences.join dropDevicePrefix_erases dropDevicePrefix_allocation
  apply hoare_modify
  intro w _
  exact no_device _ rfl

private theorem limiter : Preserves (Ready locals active) ratelimiterUninit := by
  apply RxPollOccurrences.join (erasesStatePrefix_lift _) allocationDeviceLifecycle.ratelimiter
  apply occurrence_passive
  · exact ratelimiterUninit_sameRatelimiter.of_factor (fun s => txCryptWire {dev:=s.dev}) _ (fun _=>rfl)
  · exact ratelimiterUninit_sameRatelimiter.of_factor (fun s => handoffTxView {dev:=s.dev}) _ (fun _=>rfl)

theorem destruct : Preserves (Ready [] []) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact socket_reinit _ _)
    | (rx_retention_head peerRemoveAll; exact OccurrenceRemoval.remove_all)
    | (rx_retention_head mayHaveSlept; exact RxPollOccurrences.store mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact limiter)
    | (rx_retention_head modify; exact drop)
    | (rx_retention_head retireDeviceUnits; exact RxPollOccurrences.store retireDeviceUnits_sameWGStore)
    | occurrence_config_step

theorem delete (onDown onUnregister : WG.M Unit)
    (downRule : Preserves (Ready [] []) onDown) (unregisterRule : Preserves (Ready [] []) onUnregister) :
    Preserves (Ready [] []) (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact downRule
    | exact unregisterRule
    | (rx_retention_head wgDown; exact down)
    | (rx_retention_head wgDestruct; exact destruct)
    | (rx_retention_head mayHaveSlept; exact RxPollOccurrences.store mayHaveSlept_sameWGStore)
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
    | occurrence_config_step

theorem delete_default : Preserves (Ready [] []) (wgDelete : WG.M Int) :=
  delete _ _ (preserves_pure ()) (preserves_pure ())

private theorem init_items (n : Nat) : (PtrRing.init (α := List SkbId) n).items = [] := by
  have physical : TxRing.Refines (PtrRing.init n) [] (PtrRing.init n) := ⟨[],rfl⟩
  simpa only [Ring.Journal.admitted,Ring.Journal.consumed,List.filterMap_nil,List.nil_append] using
    physical.initialized.2.1.symm

private theorem fresh (w : WGWorld)
    (peers : ∀d,w.dev=some d→d.peers={})
    (ring : ∀d,w.dev=some d→d.encryptQueue=PtrRing.init MAX_QUEUED_PACKETS) : TxOccurrences [] [] w := by
  have absent (pid : PeerId) : peerAt w pid = none := by
    cases device : w.dev with
    | none => simp [peerAt,device]
    | some d => simp [peerAt,device,peers d device]
  have empty : txCryptItems w = [] := by
    cases device : w.dev with
    | none => simp [txCryptItems,device]
    | some d => simp [txCryptItems,device,ring d device,init_items]
  constructor
  · constructor <;> simp [txLocalItems,absent]
  · constructor
    · intro d device
      rw [ring d device]
      exact ⟨_,[],⟨[],rfl⟩⟩
    · simp [empty]
    · intro items member; simp [empty] at member
    · intro items member; simp [empty] at member

theorem create : Preserves (Ready [] []) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  refine ⟨Allocated.native wgCreatePrefix_erases wgCreatePrefix_allocation before.1 a b run,?_⟩
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,new⟩
  · have wire : txCryptWire v = txCryptWire w := by
      simpa only [linkView,linkStore,linkDevice,wgStoreView,txCryptWire,TxRing.nativeCell,
        TxDisposition.txPackets,Option.map_map,Option.bind_map,Function.comp_def] using
        congrArg (fun s : WGStoreView => txCryptWire {dev:=s.dev}) same
    have queues : txQueueContents v = txQueueContents w := by
      funext pid
      simpa only [linkView,linkStore,linkDevice,wgStoreView,txQueueContents,handoffTxView,
        Option.bind_map,Function.comp_def] using
        congrArg (fun s : WGStoreView => txQueueContents {dev:=s.dev} pid) same
    exact ⟨before.2.1.queueContents queues (congrArg Prod.snd wire),
      before.2.2.frame_packets (congrArg Prod.fst wire)
        (fun _ owned => owned.queueContents queues) (congrArg Prod.snd wire)⟩
  · apply fresh v
    · intro d device
      simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
        device,Option.map_some,Option.map_map,Function.comp_def,Option.some.injEq] using
        congrArg (fun s : WGStoreView => s.dev.map Device.peers) new
    · intro d device
      simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
        device,Option.map_some,Option.map_map,Function.comp_def,Option.some.injEq] using
        congrArg (fun s : WGStoreView => s.dev.map Device.encryptQueue) new

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceLifecycle
