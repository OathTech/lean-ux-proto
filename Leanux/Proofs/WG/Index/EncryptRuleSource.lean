import Leanux.Proofs.WG.Queues.CurrentSlotWorkers
import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.EncryptCore
open Leanux Leanux.WG Queues
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem packet_preserves_source (P : World→Prop) (key : KeypairId) (packet : DataPacket)
    (padding : Preserves P
      (monadLift (calculateSkbPadding packet.plaintext.bytes.length packet.plaintext.mtu) : Leanux.M Nat))
    (checksum : ∀p,Preserves P (Env.checksumHelp p))
    (read : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair))
    (ambient : ∀{α : Type}(action : AmbientM α),Preserves P (monadLift action : Leanux.M α)) :
    Preserves P (encryptPacket Env.checksumHelp key packet) := by
  routing_tx_source [encryptPacket] using [padding,checksum,read,ambient]

theorem tail_preserves_source (P : World→Prop) (item : Option (List SkbId))
    (read : ∀id,Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket))
    (write : ∀id f,Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit))
    (enqueue : ∀xs state,Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit))
    (packet : ∀key pkt,Preserves P (encryptPacket Env.checksumHelp key pkt))
    (need : Preserves P (Env.condResched .encryptWorker))
    (ambient : ∀{α : Type}(action : AmbientM α),Preserves P (monadLift action : Leanux.M α)) :
    Preserves P (RxWorkers.encryptTailSource item) := by
  have step : Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,enqueue,packet,ambient]
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [step,need,ambient]

end Leanux.Proofs.WG.Index.EncryptCore
