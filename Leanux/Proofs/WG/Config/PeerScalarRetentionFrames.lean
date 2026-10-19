import Leanux.Proofs.WG.Config.PeerScalarRetentionModel
import Leanux.Proofs.WG.Index.StagedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.PeerScalarRetention
open Leanux Leanux.WG Noise Std.Do

def view (g : WGWorld) : Map := peerValues g.dev

theorem frame_retained {entry final : WGWorld}
    (frame : Index.StagingRich.Frame entry final) :
    Retained (view entry) (view final) := by
  let project (c : Index.StagingPreservation.PeerImage) : Cell :=
    (c.2.2.2.2.2.1,c.2.2.2.2.2.2.2.2.1,c.2.2.2.2.2.2.2.2.2.1,c.2.2.2.2.2.2.2.2.2.2)
  have mapped (g : WGWorld) (pid : PeerId) :
      view g pid=(Index.StagingRich.peerMap g pid).map project := by
    simp only [view,peerValues,Index.StagingRich.peerMap,Option.map_map,Function.comp_def]
    rfl
  intro pid value present
  rw [mapped] at present ⊢
  cases resident : Index.StagingRich.peerMap final pid with
  | none => simp [resident] at present
  | some c =>
    rw [frame.peers pid c resident]
    simpa only [resident] using present

end Leanux.Proofs.WG.Config.PeerScalarRetention
