import Leanux.Proofs.WG.Config.AllowedOrderModel

/-! Whole peer-command routing grammar. Empty histories deliberately retain their original outcome without inferring an acquisition. Nonempty histories have one target and either the requested flags or the original new-peer replacement mask. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.CommandOrder
open Leanux Leanux.WG Leanux.Proofs.WG.AllowedIps
open AllowedOrder

def EffectiveFlags (requested effective : UInt32) : Prop :=
  effective=requested ∨ effective=requested &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS

def Partial (attrs : PeerAttrs) (requested : UInt32) (events : List RoutingCompletion) : Prop :=
  events=[] ∨ ∃pid effective, EffectiveFlags requested effective ∧
    UpdatePartial attrs (some pid) effective pid events

def Finished (attrs : PeerAttrs) (requested : UInt32)
    (events : List RoutingCompletion) (ret : Int) : Prop :=
  events=[] ∨ ∃pid effective, EffectiveFlags requested effective ∧
    UpdateFinished attrs (some pid) effective pid events ret

end Leanux.Proofs.WG.Config.CommandOrder
