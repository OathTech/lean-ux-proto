import Leanux.Proofs.WG.Queues.CurrentSlotWorkers
import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.EncryptCore
open Leanux Leanux.WG Queues
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem packet_preserves_leaves (P : World→Prop) (key : KeypairId) (packet : DataPacket)
    (padding : Preserves P
      (monadLift (calculateSkbPadding packet.plaintext.bytes.length packet.plaintext.mtu) : Leanux.M Nat))
    (checksum : ∀p,Preserves P (Env.checksumHelp p))
    (read : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair))
    (cut : Preserves P (skipCut [.flowHashSecret] : Leanux.M Unit))
    (alloc : ∀site,Preserves P (hiddenAlloc site : Leanux.M Bool))
    (decision : ∀site value,Preserves P (branch site value : Leanux.M Bool)) :
    Preserves P (encryptPacket Env.checksumHelp key packet) := by
  routing_tx_source [encryptPacket] using [padding,checksum,read,cut,alloc,decision]

theorem stepTail_preserves_leaves (P : World→Prop) (item : Option (List SkbId))
    (read : ∀id,Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket))
    (write : ∀id f,Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit))
    (enqueue : ∀xs state,Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit))
    (packet : ∀key pkt,Preserves P (encryptPacket Env.checksumHelp key pkt))
    (decision : ∀site value,Preserves P (branch site value : Leanux.M Bool))
    (failure : ∀{α : Type} message,Preserves P (invariant message : Leanux.M α)) :
    Preserves P (RxWorkers.encryptStepTailSource item) := by
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,enqueue,packet,decision,failure]

theorem tail_preserves_leaves (P : World→Prop) (item : Option (List SkbId))
    (read : ∀id,Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket))
    (write : ∀id f,Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit))
    (enqueue : ∀xs state,Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit))
    (packet : ∀key pkt,Preserves P (encryptPacket Env.checksumHelp key pkt))
    (need : Preserves P (Env.condResched .encryptWorker))
    (decision : ∀site value,Preserves P (branch site value : Leanux.M Bool))
    (failure : ∀{α : Type} message,Preserves P (invariant message : Leanux.M α)) :
    Preserves P (RxWorkers.encryptTailSource item) := by
  have step := stepTail_preserves_leaves P item read write enqueue packet decision failure
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [step,need,decision]

theorem packet_preserves_source (P : World→Prop) (key : KeypairId) (packet : DataPacket)
    (padding : Preserves P
      (monadLift (calculateSkbPadding packet.plaintext.bytes.length packet.plaintext.mtu) : Leanux.M Nat))
    (checksum : ∀p,Preserves P (Env.checksumHelp p))
    (read : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair))
    (ambient : ∀{α : Type}(action : AmbientM α),Preserves P (monadLift action : Leanux.M α)) :
    Preserves P (encryptPacket Env.checksumHelp key packet) := by
  exact packet_preserves_leaves P key packet padding checksum read (ambient _)
    (fun _=>ambient _) (fun _ _=>ambient _)

theorem tail_preserves_source (P : World→Prop) (item : Option (List SkbId))
    (read : ∀id,Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket))
    (write : ∀id f,Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit))
    (enqueue : ∀xs state,Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit))
    (packet : ∀key pkt,Preserves P (encryptPacket Env.checksumHelp key pkt))
    (need : Preserves P (Env.condResched .encryptWorker))
    (ambient : ∀{α : Type}(action : AmbientM α),Preserves P (monadLift action : Leanux.M α)) :
    Preserves P (RxWorkers.encryptTailSource item) := by
  exact tail_preserves_leaves P item read write enqueue packet need
    (fun _ _=>ambient _) (fun _=>ambient _)

end Leanux.Proofs.WG.Index.EncryptCore
