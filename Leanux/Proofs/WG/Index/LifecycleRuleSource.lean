import Leanux.Proofs.WG.Noise.DriverTagProductSource
import Leanux.Proofs.WG.Noise.DriverTagSilentFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.LifecycleSource
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do Queues

theorem open_preserves (P : WGWorld → Prop)
    (read : Preserves P getDev)
    (peer : ∀pid, Preserves P (getPeer pid))
    (socket : ∀port, Preserves P (socketInit port))
    (staged : ∀pid, Preserves P (sendStagedPackets pid))
    (keepalive : ∀pid, Preserves P (sendKeepalive pid)) :
    Preserves P wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head getDev; exact read)
    | (rx_retention_head getPeer; exact peer _)
    | (rx_retention_head socketInit; exact socket _)
    | (rx_retention_head sendStagedPackets; exact staged _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id P
       intro x acc
       change Preserves P _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step


theorem preexit_preserves (P : WGWorld → Prop)
    (read : Preserves P (get : WG.M WGWorld))
    (device : Preserves P getDev)
    (detach : Preserves P (modifyDev fun d => {d with carrier:=false,creatingNet:=false}))
    (socket : Preserves P (socketReinit none none))
    (endpoint : ∀pid,Preserves P (clearPeerEndpointSrc pid)) :
    Preserves P netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head get; exact read)
    | (rx_retention_head getDev; exact device)
    | (rx_retention_head modifyDev; exact detach)
    | (rx_retention_head socketReinit; exact socket)
    | (rx_retention_head clearPeerEndpointSrc; exact endpoint _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id P
       intro x acc
       change Preserves P _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem envUp_preserves (P : World → Prop)
    (frames : ∀{α : Type}(action : Leanux.M α), SameProductStore action → Preserves P action)
    (up : Preserves P (liftWG WG.wgUp)) :
    Preserves P Env.wgUp := by
  unfold Env.wgUp
  repeat' first
    | (rx_retention_head getWG; exact frames _ (fun initial=>productGetWG_spec (fun s=>s=initial)))
    | (rx_retention_head modifyEnv
       apply frames
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w result v run
       cases run
       rfl)
    | (allocation_release_lift_from WG.M; exact up)
    | (allocation_release_lift_from Net.M
       apply frames
       exact fun initial => productRouting_spec _ (fun s=>s=initial))
    | (rx_retention_head skipCut
       apply frames
       intro initial
       exact productAmbient_spec (AmbientM.skipCut _) _ (fun _ _ pre=>pre))
    | (allocation_release_lift_from AmbientM
       apply frames
       intro initial
       exact productAmbient_spec _ _ (fun _ _ pre=>pre))
    | rx_retention_step

end Leanux.Proofs.WG.Noise.LifecycleSource
