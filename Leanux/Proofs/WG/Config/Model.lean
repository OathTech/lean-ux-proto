import Leanux.WG.Types

/-! Pure configuration observations and store transformations. -/
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

def clearedSource (p : Peer) (reset : UInt64) : Peer :=
  { p with
    endpoint := p.endpoint.map fun e => { e with src := 0, srcIf := 0 }
    dstCache := { p.dstCache with resetTs := reset, slot := none } }

def sourceClear (p : Peer) : Prop :=
  (∀ e, p.endpoint = some e → e.src = 0 ∧ e.srcIf = 0) ∧ p.dstCache.slot = none

/-- All device fields except the peer-store representation. -/
def withoutPeers (d : Device) : Device := { d with peers := {} }

end Leanux.Proofs.WG.Config
