import Leanux.Proofs.WG.TransmitSecurity.EncryptSource
import Leanux.Proofs.Framing.WGData
import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames

/-! Key-store framing before the native AEAD read. The concrete checksum
callback is pure with respect to native state; arbitrary callbacks are not. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Encryption
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

def keys (w : WGWorld) := w.dev.map (·.keypairs)
def productKeys (w : World) := keys w.wg

theorem prepare_keys (pkt : DataPacket) :
    SameView productKeys (prepare Env.checksumHelp pkt) := by
  intro initial
  let P := fun w : World => productKeys w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have checksum (p : Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    (sameView_liftWG productKeys keys _
      ((calculateSkbPadding_sameWGWorld _ _).factor keys) (fun _ _ _ same => same)).wp (· = initial)
  change Preserves P _
  routing_tx_source [prepare] using [padding,checksum,ambient]

end Leanux.Proofs.WG.TransmitSecurity.Encryption
