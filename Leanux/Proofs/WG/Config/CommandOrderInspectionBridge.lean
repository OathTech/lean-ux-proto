import Leanux.Proofs.WG.Config.CommandOrderSource

/-! Projected inspection of the original routing observer. Native witnesses are confined to the source bridge. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.CommandOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise
open Leanux.Proofs.Framing Lifetimes Std.Do
open AllowedOrder

def inspection (attrs : PeerAttrs) (w : WGWorld) (ambient : Ambient) : Inspection :=
  let result:=runWGPrefix (setPeerCmdObserved attrs) w ambient []
  ⟨Campaign2.observeResult result.1,result.2⟩

def Matches (attrs : PeerAttrs) (entry : Campaign2.Snapshot) (result : Inspection) : Prop :=
  ∃w ambient,Campaign2.snapshot w ambient=entry ∧ inspection attrs w ambient=result

def Facts (attrs : PeerAttrs) (entry : Campaign2.Snapshot) (result : Inspection) : Prop :=
  Matches attrs entry result ∧
  Partial attrs (attrs.flags.getD 0) result.completions ∧
  match result.outcome with
  | .error _=>True
  | .ok (ret,_)=>Finished attrs (attrs.flags.getD 0) result.completions ret

end Leanux.Proofs.WG.Config.CommandOrder
