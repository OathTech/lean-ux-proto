import Leanux.Proofs.WG.Config.GetterMetadataModel
import Leanux.Proofs.WG.Noise.CookieReplyTagFrames

/-! Configuration readback projects the owned socket frame. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG TimerDiscipline Noise Std.Do

def getterMetadata (g : WGWorld) : GetterMetadata :=
  g.dev.map fun d => (sendConfiguration d, g.nlSock7, g.fixtureNetDevices)

theorem getterMetadata_observation (g : WGWorld) (ambient : Ambient) :
    getterMetadata g = getterMetadataObservation (Campaign2.snapshot g ambient) := rfl

theorem getterMetadata_frame_of_sendWork {α : Type} (action : WG.M α) (pid : PeerId)
    (frame : ∀ (q : Option SendWorkDevice) (v : Option SendWorkPeer),
      ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄) (entry : GetterMetadata) :
    Ensures action (fun g => getterMetadata g = entry)
      (fun _ g => getterMetadata g = entry) := by
  intro g ambient result final after pre run
  have same := (ensures_iff _ _ _).mpr
    (frame (sendWorkAt g pid).1 (sendWorkAt g pid).2)
    g ambient result final after rfl run
  have projected := congrArg (fun x : SendWorkView =>
    x.1.map (fun d => d.2.2.2)) same
  have metadata : getterMetadata final = getterMetadata g := by
    simpa [getterMetadata, sendWorkAt, sendWorkKernel, sendWorkDevice,
      Option.map_map, Function.comp_def] using projected
  exact metadata.trans pre

theorem sendBufferToPeer_getterMetadata (pid : PeerId) (bytes : List UInt8)
    (entry : GetterMetadata) :
    Ensures (sendBufferToPeer pid bytes) (fun g => getterMetadata g = entry)
      (fun _ g => getterMetadata g = entry) :=
  getterMetadata_frame_of_sendWork _ pid (sendBufferToPeer_spec_sendWork_variant pid bytes) entry

theorem sendBufferAsReplyToSkb_getterMetadata (src : SkbSource) (bytes : List UInt8)
    (entry : GetterMetadata) :
    Ensures (sendBufferAsReplyToSkb src bytes) (fun g => getterMetadata g = entry)
      (fun _ g => getterMetadata g = entry) :=
  getterMetadata_frame_of_sendWork _ 0
    (Noise.sendBufferAsReplyToSkb_sendWorkView 0 src bytes) entry

end Leanux.Proofs.WG.Config

