import Leanux.Proofs.WG.Config.AllowedOrderSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.AllowedOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise
open Leanux.Proofs.Framing Lifetimes Std.Do

def inspection (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (w : WGWorld) (ambient : Ambient) : Inspection :=
  let result:=runWGPrefix (peerConfigUpdateObserved attrs peer flags psk pid) w ambient []
  ⟨Campaign2.observeResult result.1,result.2⟩

def Matches (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (entry : Campaign2.Snapshot) (result : Inspection) : Prop :=
  ∃w ambient,Campaign2.snapshot w ambient=entry ∧
    inspection attrs peer flags psk pid w ambient=result

def Facts (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (entry : Campaign2.Snapshot) (result : Inspection) : Prop :=
  Matches attrs peer flags psk pid entry result ∧
  UpdatePartial attrs peer flags pid result.completions ∧
  match result.outcome with
  | .error _=>True
  | .ok (ret,_)=>UpdateFinished attrs peer flags pid result.completions ret

end Leanux.Proofs.WG.Config.AllowedOrder
