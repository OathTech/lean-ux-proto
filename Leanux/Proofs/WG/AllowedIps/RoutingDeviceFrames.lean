import Leanux.Proofs.WG.AllowedIps.RoutingFlushFrames
import Leanux.Proofs.Framing.WGConfiguration
import Leanux.Proofs.Framing.WGSocketLifecycle
import Leanux.Proofs.Framing.Product

/-! Concrete routing frames for device configuration. Strong existing masks
project to the routing view; peer/key helpers retain their original getters and
Stops. These normal-endpoint frames assert neither progress nor residency. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-- The original product observation masks only the configuration fields of
the device; the remaining store observations retain their original scope. -/
def configurationProductView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter),
    {wgStoreView w.wg with dev := w.wg.dev.map configurationDevice})

/-- The socket mask has the same original product observation domain. -/
def socketControlProductView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter),
    {wgStoreView w.wg with dev := w.wg.dev.map socketDevice})

theorem configuration_routing (a : Leanux.M α)
    (ha : SameView configurationProductView a) :
    SameView (fun w => routingView w.wg) a := by
  apply ha.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w => routingView w.wg)
  intro w
  simp [routingView, configurationProductView, configurationDevice,
    routingState, Option.map_map, Function.comp_def]
  rfl

theorem socketControl_routing (a : Leanux.M α)
    (ha : SameView socketControlProductView a) :
    SameView (fun w => routingView w.wg) a := by
  apply ha.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w => routingView w.wg)
  intro w
  simp [routingView, socketControlProductView, socketDevice,
    routingState, Option.map_map, Function.comp_def]
  rfl

theorem configuration_routing_native (a : WG.M α) (ha : SameConfiguration a) :
    SameView routingView a := by
  apply ha.of_factor (fun k : WGOwnedView => k.dev.map routingState) routingView
  intro w
  simp [routingView, configurationView, configurationDevice,
    routingState, Option.map_map, Function.comp_def]
  rfl

theorem socketControl_routing_native (a : WG.M α) (ha : SameSocket a) :
    SameView routingView a := by
  apply ha.of_factor (fun k : WGOwnedView => k.dev.map routingState) routingView
  intro w
  simp [routingView, socketView, socketDevice,
    routingState, Option.map_map, Function.comp_def]
  rfl

theorem dstCacheResetNow_routing (pid : PeerId) : SameView routingView (dstCacheResetNow pid) := by
  apply (dstCacheReset_routing pid).bind
  intro _
  exact modifyPeer_routing pid (fun p => {p with dstCache := {p.dstCache with slot := none}}) (fun _ => rfl)

theorem clearPeerEndpointSrc_routing (pid : PeerId) : SameView routingView (clearPeerEndpointSrc pid) := by
  simpa only [clearPeerEndpointSrc, bind_assoc] using
    (modifyPeer_routing pid
      (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}})
      (fun _ => rfl)).bind (fun _ => dstCacheResetNow_routing pid)

theorem setPort_routing (port : Nat) : SameView routingView (setPort port) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  have read : Preserves P getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hp hr
    cases hd : w.dev <;> simp [getDev, hd, invariant, AmbientM.invariant] at hr
    · cases hr
    · rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hp
  have hb (d : Decision) (b : Bool) : Preserves P (branch d b : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch d b) P
  have hc := fun pid => (clearPeerEndpointSrc_routing pid).wp (fun t => t = initial)
  have hs := (socketControl_routing_native _ (socketInit_sameSocket port)).wp (fun t => t = initial)
  have hm := (modifyDev_routing (fun d => {d with incomingPort := port}) (fun _ => rfl)).wp (fun t => t = initial)
  change Preserves P (setPort port)
  unfold setPort
  apply preserves_bind read
  intro d
  apply preserves_bind (hb _ _)
  intro same
  cases same
  · dsimp only
    apply preserves_bind
    · exact list_view_spec routingView (fun t => t = initial) d.peerList () _
        (fun pid _ => preserves_bind (hb _ _) (fun _ =>
          preserves_bind (hc pid) (fun _ => preserves_pure _)))
    intro _
    apply preserves_bind (hb _ _)
    intro _
    apply preserves_bind (hb _ _)
    intro stopped
    cases stopped
    · exact hs
    · exact preserves_bind hm (fun _ => preserves_pure _)
  · exact preserves_pure _

theorem expireCurrentPeerKeypairs_routing (pid : PeerId) :
    SameView routingView (expireCurrentPeerKeypairs pid) := by
  apply SameView.of_wp
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  have hn := (requireNotPending_routing pid "clearing the handshake").wp (fun t => t = initial)
  have hr := (resetLastSentHandshake_routing pid).wp (fun t => t = initial)
  have hp := (getPeer_routing pid).wp (fun t => t = initial)
  have hg := fun kp => (getKeypair_routing kp).wp (fun t => t = initial)
  have hs := fun kp k => (setKeypair_routing kp k).wp (fun t => t = initial)
  have hclear := (handshakeClear_routing pid).wp (fun t => t = initial)
  have hb (d : Decision) (b : Bool) : Preserves P (branch d b : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch d b) P
  have hi {α : Type} (message : String) : Preserves P (invariant message : WG.M α) :=
    hoare_liftAmbient (AmbientM.invariant message) P
  have invalidated (kp : KeypairId) :
      Preserves P (do
        let k ← getKeypair kp
        setKeypair kp {k with sending := {k.sending with isValid := false}}) :=
    preserves_bind (hg kp) (fun k => hs kp _)
  have currentTail (p : Peer) : Preserves P (do
      if ← branch .expireCurrentKeypair p.keypairCurrent.isSome then
        let some kp := p.keypairCurrent | invariant "unreachable"
        let k ← getKeypair kp
        setKeypair kp {k with sending := {k.sending with isValid := false}}) := by
    apply preserves_bind (hb _ _)
    intro current
    cases current <;> dsimp only
    · exact preserves_pure _
    · cases p.keypairCurrent <;> dsimp only
      · exact hi _
      · exact invalidated _
  change Preserves P (expireCurrentPeerKeypairs pid)
  unfold expireCurrentPeerKeypairs
  apply preserves_bind hn
  intro _
  apply preserves_bind hclear
  intro _
  apply preserves_bind hr
  intro _
  apply preserves_bind hp
  intro p
  apply preserves_bind (hb _ _)
  intro next
  cases next <;> dsimp only
  · exact currentTail p
  · cases p.keypairNext <;> dsimp only
    · exact hi _
    · exact preserves_bind (invalidated _) (fun _ => currentTail p)

end Leanux.Proofs.WG.AllowedIps
