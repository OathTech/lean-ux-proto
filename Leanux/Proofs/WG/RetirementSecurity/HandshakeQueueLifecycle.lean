import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueConfigurationFrames
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueWorker
import Leanux.Proofs.WG.RetirementSecurity.TxWorkDeviceLifetime

/-! Native down/up preserve carried ring cells. Device construction starts a
fresh empty ring; native destruction returns no device. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option pp.structureInstances false

theorem open_cell : SameView view wgOpen := by
  handshake_cell_source [wgOpen] using [socket_init_cell,sendStagedPackets_cell,sendKeepalive_cell]

theorem up_cell : SameView view wgUp := by
  handshake_cell_source [wgUp] using [open_cell]

theorem stop_cell : SameView view wgStop := by
  handshake_cell_source [wgStop,resetLastSentHandshake]
    using [requireNotPending_cell,purge_cell,timers_stop_cell,handshake_clear_cell,key_clear_cell,socket_reinit_cell]

theorem down_cell : SameView view wgDown := by
  handshake_cell_source [wgDown] using [stop_cell]

theorem destruct (Valid : List UInt8 → Prop) : Preserves (Inv Valid) wgDestruct := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b _ run
  cases value
  intro d found
  rw [TxWork.destruct_absent run] at found
  cases found

theorem create (Valid : List UInt8 → Prop) : Preserves (Inv Valid) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  have endpoint:=(hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w)) w a value v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · apply transport _ before
    simpa only [view,linkView,linkStore,linkDevice,wgStoreView,Option.map_map,Function.comp_def] using
      congrArg (fun store : WGStoreView=>store.dev.map Device.handshakeQueue) same
  · intro d found
    have ring : d.handshakeQueue=PtrRing.init MAX_QUEUED_INCOMING_HANDSHAKES := by
      simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
        found,Option.map_some,Option.map_map,Function.comp_def,Option.some.injEq] using
        congrArg (fun store : WGStoreView=>store.dev.map Device.handshakeQueue) fresh
    rw [ring]
    exact initial _ _

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
