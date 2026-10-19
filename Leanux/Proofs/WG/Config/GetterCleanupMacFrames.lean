import Leanux.Proofs.WG.Config.GetterMetadataFrames
import Leanux.Proofs.WG.Noise.MacSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterCleanup
open Leanux Leanux.WG Noise TimerDiscipline Std.Do Leanux.Proofs.Framing

theorem mac (pid : PeerId) (msg : List UInt8) :
    SameView getterMetadata (addMacToPacket pid msg) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  apply addMacToPacket_preserves pid msg (fun g => getterMetadata g = entry)
  intro p g a x v b pre run
  change Except.ok (((), {g with dev := g.dev.map (fun (d : Device) =>
    {d with peers := d.peers.insert pid _})}), a) = _ at run
  cases run
  simpa only [getterMetadata,Option.map_map,Function.comp_def,sendConfiguration] using pre.1

end Leanux.Proofs.WG.Config.GetterCleanup

