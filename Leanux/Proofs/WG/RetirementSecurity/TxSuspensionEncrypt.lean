import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionAllocation
import Leanux.Proofs.WG.RetirementSecurity.TxActorTransmit

/-! The actual encryption byte loop and publication retain suspended TX
actors; allocation draws and checksum handling use their native frames. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem padding (len mtu : Nat) : Keeps (calculateSkbPadding len mtu) := by
  suspension_source [calculateSkbPadding] using [branch, compare]

theorem choose_cpu (pid : PeerId) : Keeps (cpumaskChooseOnline pid) := by
  suspension_source [cpumaskChooseOnline] using [peer, set_peer, branch, compare]

theorem publish (items : List SkbId) (state : PacketState) : Keeps (enqueuePerPeerTx items state) := by
  suspension_source [enqueuePerPeerTx] using [invariant, packet, owner_deref, peer_get, peer,
    set_packet, choose_cpu, device, peek_queued, record_queued, modify_device, peer_put]

theorem poll : Keeps TxRing.pollSource := by
  suspension_source [TxRing.pollSource] using [device, modify_device]

def suspended (w : World) := w.ambient.suspended

theorem product_ambient {action : AmbientM α} (frame : SameView Ambient.suspended action) :
    SameView suspended (monadLift action : Leanux.M α) :=
  (TxActorFrames.lift_ambient frame).factor Prod.snd

theorem encrypt_packet (kid : KeypairId) (pkt : DataPacket) :
    SameView suspended (encryptPacket Env.checksumHelp kid pkt) := by
  intro initial
  let P := fun w : World=>suspended w=initial
  have cut (sites : List HiddenSite) : Preserves P (skipCut sites : Leanux.M Unit) :=
    product_ambient (cut_ambient sites) initial
  have draw (site : AllocSite) : Preserves P (hiddenAlloc site : Leanux.M Bool) :=
    product_ambient (allocation_outcome site) initial
  have decision (which : Decision) (value : Bool) : Preserves P (Leanux.branch which value : Leanux.M Bool) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
    exact before
  have key_read (slot : KeypairId) : Preserves P (monadLift (getKeypair slot) : Leanux.M Keypair) :=
    product (key slot) initial
  have pad (len mtu : Nat) : Preserves P (monadLift (calculateSkbPadding len mtu) : Leanux.M Nat) :=
    product (padding len mtu) initial
  have checksum (packet : Packet) : Preserves P (Env.checksumHelp packet) :=
    (checksumHelp_sameWorld packet).wp P
  change Preserves P _
  routing_tx_source [encryptPacket] using [cut,draw,decision,key_read,pad,checksum]

theorem encryption_tail (item : Option (List SkbId)) :
    SameView suspended (RxWorkers.encryptStepTailSource item) := by
  intro initial
  let P := fun w : World=>suspended w=initial
  have read (skb : SkbId) : Preserves P (monadLift (getTxSkb skb) : Leanux.M DataPacket) :=
    product (packet skb) initial
  have write (skb : SkbId) (f : DataPacket→DataPacket) :
      Preserves P (monadLift (setTxSkb skb f) : Leanux.M Unit) :=
    product (set_packet skb f) initial
  have crypt (key : KeypairId) (value : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key value) := encrypt_packet key value initial
  have publication (items : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx items state) : Leanux.M Unit) :=
    product (publish items state) initial
  have decision (which : Decision) (value : Bool) : Preserves P (Leanux.branch which value : Leanux.M Bool) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
    exact before
  have stopped {α : Type} (why : String) : Preserves P (Leanux.invariant why : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,crypt,publication,decision,stopped]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
