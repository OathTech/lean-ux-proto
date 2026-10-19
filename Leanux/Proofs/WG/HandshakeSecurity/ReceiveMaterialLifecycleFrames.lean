import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialConfigurationFrames
import Leanux.Proofs.Framing.WGDeviceLifecycle
import Leanux.Proofs.WG.Queues.DeviceAuxEntry

/-! Lifecycle changes retain received allocation certificates for surviving
cells. Destruction and device creation discharge obligations by empty stores,
including the resident numeric key-slot bound. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.LifecycleFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TransmitSecurity Responder
open HandshakeFrames TimerFrames ConfigurationFrames
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def fields (w : WGWorld) := w.dev.map fun d => (d.ifindex,d.rxSkbs,d.nextKeypairId,d.keypairs)

theorem transfer (before : Bounded h w) (same : fields v = fields w) : Bounded h v := by
  cases hw : w.dev with
  | none =>
    cases hv : v.dev with
    | none => simpa only [Bounded,Inv,KeyBounds,Certificate,packetStamp,pool,hw,hv] using before
    | some d => simp [fields,hw,hv] at same
  | some d =>
    cases hv : v.dev with
    | none => simp [Bounded,Inv,KeyBounds,hv]
    | some e =>
      have eq : e.ifindex = d.ifindex ∧ e.rxSkbs = d.rxSkbs ∧ e.nextKeypairId = d.nextKeypairId ∧ e.keypairs = d.keypairs := by
        simpa only [fields,hw,hv,Option.map_some,Option.some.injEq,Prod.mk.injEq] using same
      simpa only [Bounded,Inv,KeyBounds,Certificate,packetStamp,pool,hw,hv,Option.bind_some,
        Option.map_some,Option.some.injEq,forall_eq,forall_eq',eq.1,eq.2.1,eq.2.2.1,eq.2.2.2] using before

macro "receive_lifecycle_frame" : tactic => `(tactic| first
  | (rx_retention_head purgeStagedPackets; exact purge _)
  | (rx_retention_head timersStop; exact stop_timers _)
  | (rx_retention_head handshakeClear; exact handshake_clear _)
  | (rx_retention_head keypairsClear; exact keys_clear _)
  | (rx_retention_head resetLastSentHandshake; exact reset_handshake _)
  | (rx_retention_head socketReinit; exact socket_frame (socketReinit_sameSocket _ _))
  | receive_configuration_frame)

theorem stop : Preserves (Bounded h) wgStop := by
  unfold wgStop requireNotPending
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' receive_lifecycle_frame

theorem down : Preserves (Bounded h) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop)
    | receive_lifecycle_frame

theorem pre_exit : Preserves (Bounded h) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' receive_lifecycle_frame

theorem absent (w : WGWorld) (empty : w.dev = none) : Bounded h w := by
  constructor <;> intro d device <;> rw [empty] at device <;> cases device

private theorem limiter : Preserves (Bounded h) ratelimiterUninit := by
  have same : SameView (fun w : WGWorld => w.dev) ratelimiterUninit :=
    ratelimiterUninit_sameRatelimiter.of_factor (fun s : WGStoreView => s.dev) _ (fun _ => rfl)
  exact same.wp (fun dev => Bounded h {dev:=dev})

theorem destruct : Preserves (Bounded h) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head mayHaveSlept; exact bounded_store mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact limiter)
    | (rx_retention_head _root_.modify; apply hoare_modify; intro w _; exact absent _ rfl)
    | (rx_retention_head retireDeviceUnits; exact bounded_store retireDeviceUnits_sameWGStore)
    | receive_lifecycle_frame

theorem delete (onDown onUnregister : WG.M Unit)
    (downRule : Preserves (Bounded h) onDown) (unregisterRule : Preserves (Bounded h) onUnregister) :
    Preserves (Bounded h) (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact downRule
    | exact unregisterRule
    | (rx_retention_head wgDown; exact down)
    | (rx_retention_head wgDestruct; exact destruct)
    | (rx_retention_head mayHaveSlept; exact bounded_store mayHaveSlept_sameWGStore)
    | receive_lifecycle_frame

theorem delete_default : Preserves (Bounded h) (wgDelete : WG.M Int) :=
  delete _ _ (preserves_pure ()) (preserves_pure ())

theorem device_create : Preserves (Bounded h) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · apply transfer before
    have projected := congrArg (fun s : WGStoreView => fields {dev:=s.dev}) same
    simpa only [fields,linkView,linkStore,wgStoreView,linkDevice,Option.map_map,Function.comp_def] using projected
  · have projected := congrArg (fun s : WGStoreView => s.dev.map fun d => (d.rxSkbs,d.keypairs)) fresh
    constructor
    · intro d hd id packet stored _
      have empty : d.rxSkbs = {} := by
        simpa only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,hd,
          Option.map_some,Option.some.injEq,Prod.mk.injEq] using (congrArg (Option.map Prod.fst) projected)
      simp [empty] at stored
    · intro d hd slot key stored
      have empty : d.keypairs = {} := by
        simpa only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,hd,
          Option.map_some,Option.some.injEq,Prod.mk.injEq] using (congrArg (Option.map Prod.snd) projected)
      simp [empty] at stored

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.LifecycleFrames
