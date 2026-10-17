import Leanux.Proofs.WG.Config.MixedPageContentModel
import Leanux.Proofs.WG.Config.MixedPageSelectionModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Complete fixed Device fields and every original peer/node occurrence, in
order, with the original stored-width and endpoint serialization. -/
def mixedGetterJson (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode) : Json :=
  Json.mkObj (deviceFixedAttrs d ++ [("peers",Json.arr
    ((mixedRowsParts peers nodes {hasWg := true} (mixedInitialRows d peers)).toArray.map
      fun p => Json.mkObj p.attrs))])

end Leanux.Proofs.WG.Config
