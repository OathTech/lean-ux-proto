import Leanux.Proofs.WG.Config.RequestOrderFrames
import Leanux.Proofs.WG.Config.RequestKeyHeaderEffects
import Leanux.Proofs.WG.Config.GetterContextClaims

/-! Physical header projections across socket effects, endpoint-source clearing and the original port setter. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
open Leanux Leanux.WG Noise TimerDiscipline
open Leanux.Proofs.Framing Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

def nativeFixed (g : WGWorld) := g.dev.map fixed

theorem fixed_socket {α : Type} {action : WG.M α} (frame : SameSocket action) :
    SameView nativeFixed action :=
  frame.of_factor (fun s : WGOwnedView=>s.dev.map fixed) nativeFixed (fun g=>by
    simp only [socketView,wgOwnedView,wgStoreView,nativeFixed,Option.map_map,Function.comp_def]
    rfl)

theorem fixed_metadata {α : Type} {action : WG.M α}
    (frame : SameView getterMetadata action) : SameView nativeFixed action :=
  frame.of_factor (fun m=>m.map (fun v=>
    (v.1.1,v.1.2.1,0,v.1.2.2.2.1,v.1.2.2.2.2.1,v.1.2.2.2.2.2))) nativeFixed
    (fun g=>by simp only [getterMetadata,nativeFixed,Option.map_map,Function.comp_def]; rfl)

theorem clear_fixed (pid : PeerId) : SameView nativeFixed (clearPeerEndpointSrc pid) :=
  (show SameView (fun g : WGWorld=>g.dev.map withoutPeers) (clearPeerEndpointSrc pid)
    from fun initial=>clearEndpointSource_device_frame pid initial).of_factor
    (fun d=>d.map fixed) nativeFixed (fun g=>by
      simp only [nativeFixed,Option.map_map,Function.comp_def]; rfl)

theorem port_fixed (port : Nat) : SameView nativeFixed (setPort port) := by
  have edit : SameSocket (modifyDev (fun d=>{d with incomingPort:=port})) :=
    fun initial=>modifyDev_socket_spec (fun x=>x=initial) _ (fun _=>rfl)
  intro initial
  change Preserves (fun g=>nativeFixed g=initial) _
  unfold setPort
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc
       exact (clear_fixed _).wp (fun x=>x=initial))
    | (rx_retention_head socketInit
       exact (fixed_socket (socketInit_sameSocket _)).wp (fun x=>x=initial))
    | (rx_retention_head getDev
       exact (Internal.getDev_frame.factor nativeFixed).wp (fun x=>x=initial))
    | (rx_retention_head modifyDev
       exact (fixed_socket edit).wp
         (fun x=>x=initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun g=>nativeFixed g=initial)
       intro x b
       change Preserves (fun g=>nativeFixed g=initial) _)
    | rx_retention_step

end Leanux.Proofs.WG.Config.RequestOrder.KeyHeader
