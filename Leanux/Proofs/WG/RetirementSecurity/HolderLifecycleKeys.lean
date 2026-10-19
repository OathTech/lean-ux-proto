import Leanux.Proofs.WG.RetirementSecurity.HolderOuterTraffic
import Leanux.Proofs.WG.RetirementSecurity.HolderDeviceConfiguration

/-! Native lifecycle boundaries preserve exact key credit. Creation installs
an empty key store; shutdown pays the actual slots while keeping outstanding
packet references. Endpoint reset is restricted to an empty local ledger. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderLifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem absent (w : WGWorld) (none : w.dev=Option.none) : HolderAccount [] w := by
  refine ⟨[],by simp [durableLoans,none],?_⟩
  intro allocation
  simp [Credits.balance,keyAt,none]

theorem fresh (w : WGWorld) (emptyPeers : ∀d,w.dev=some d→d.peers={})
    (emptyKeys : ∀d,w.dev=some d→d.keypairs={}) : HolderAccount [] w := by
  cases device:w.dev with
  | none=>exact absent w device
  | some d=>
    refine ⟨[],by simp [durableLoans,device,emptyPeers d device]; rfl,?_⟩
    intro allocation
    simp [Credits.balance,keyAt,device,emptyKeys d device]

theorem link_points (w : WGWorld) : ownershipPointView {dev:=(linkView w).dev}=ownershipPointView w := by
  unfold ownershipPointView ownershipAt peerAt packetKeyWords keyReferenceView keyAt
  simp only [linkView,linkStore,linkDevice,wgStoreView,Option.bind_map,Function.comp_def,Option.isSome_map]

theorem create : Preserves (HolderAccount []) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w)) w a result v b rfl run
  rcases endpoint with same | ⟨_,new⟩
  · apply entry.points
    simpa only [link_points] using congrArg (fun s:WGStoreView=>ownershipPointView {dev:=s.dev}) same
  · apply fresh v
    · intro d device
      simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
        device,Option.map_some,Option.some.injEq] using congrArg (fun s:WGStoreView=>s.dev.map Device.peers) new
    · intro d device
      simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
        device,Option.map_some,Option.some.injEq] using congrArg (fun s:WGStoreView=>s.dev.map Device.keypairs) new

theorem socket (port : Nat) : Preserves (HolderKeepalive.Ready temporary) (socketInit port) :=
  HolderDevice.join (HolderResponse.points (DeviceControlCall.erases (.init port))
    (DeviceControlCall.allocation (.init port)) (HolderDevice.socket_points (socketInit_sameSocket port)))
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotDevice.«0».Leanux.Proofs.WG.CurrentSlots.Device.socket)
      (socketInit_sameSocket port))

theorem running (value : Bool) : Preserves (HolderKeepalive.Ready temporary)
    (modifyDev fun d=>{d with running:=value}) := by
  apply HolderDevice.join (HolderResponse.points (erasesStatePrefix_lift _)
    (allocationDeviceControl.running value)
    (ownership_modifyDev (fun d=>{d with running:=value}) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)))
  apply CurrentSlots.fields_preserves (project:=id)
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  unfold CurrentSlots.fields RxCredits.keyWords
  simp only [id_eq,Option.map_map,Option.bind_map,Function.comp_def]

theorem open_device : Preserves (HolderKeepalive.Ready temporary) wgOpen := by
  unfold wgOpen
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket _)
    | (rx_retention_head sendStagedPackets; exact HolderKeepalive.staged _)
    | (rx_retention_head sendKeepalive; exact HolderKeepalive.keepalive _)
    | (rx_retention_head getDev; exact HolderDevice.store getDev_sameWGStore)
    | (rx_retention_head getPeer; exact getPeer_preserves _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (HolderKeepalive.Ready temporary)
       intro x u
       change Preserves (HolderKeepalive.Ready temporary) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem up : Preserves (HolderKeepalive.Ready temporary) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_device)
    | (rx_retention_head modifyDev; exact running _)
    | rx_retention_step

theorem down_keys (entry : HolderBoundary.Entry temporary carriers loans w) (a b : Ambient)
    (run : (wgDown.run w).run a=.ok (((),v),b)) : HolderAccount temporary v := by
  obtain ⟨holders,funded,stable⟩ := entry.2.1.1.1
  have anchors := KeySlotLiveness.references entry.2.2 funded entry.2.1.1.2.1 entry.2.1.1.2.2
  exact ((hoare_iff_run_ambient _ _ _).mp HolderShutdown.down w a () v b
    (HolderDrain.initial entry.1.1 funded stable anchors) run).2.1

theorem down : Preserves (HolderBoundary.Entry temporary carriers loans) wgDown := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  cases result
  have peer := (hoare_iff_run_ambient _ _ _).mp DeviceAuxEntry.down w a () v b entry.2.1 run
  exact ⟨⟨down_keys entry a b run,Allocated.native (DeviceControlCall.erases .down)
      (DeviceControlCall.allocation .down) entry.1.2.1 a b run,peer.2.2⟩,peer,
    (hoare_iff_run_ambient _ _ _).mp (KeySlotLiveness.down (pending:=[])) w a () v b entry.2.2 run⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderLifecycle
