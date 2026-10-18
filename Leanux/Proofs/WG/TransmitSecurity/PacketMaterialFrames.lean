import Leanux.Proofs.WG.Queues.TxItemSeparation
import Leanux.Proofs.WG.Queues.RxWorkerCuts
import Leanux.Proofs.WG.TransmitSecurity.EncryptFrames
import Leanux.Proofs.WG.Packets.PublicationPoll

/-! TX scheduling marks and encrypted bytes do not change the packet's
selected peer, key slot, nonce or original plaintext. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketMaterial
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition

def material (p : DataPacket) : DataPacket := {p with state := .uncrypted,bytes := []}
def view (w : WGWorld) (id : SkbId) : Option DataPacket := (txPackets w id).map material

theorem of_packets {a : WG.M α} (h : SameView txPackets a) : SameView view a :=
  h.factor (fun f id => (f id).map material)

theorem read_tx (id : SkbId) : SameView view (getTxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a packet v b run
  exact congrArg view (Packets.getTxSkb_current id w v packet a b run).1

theorem read_peer (id : PeerId) : SameView view (getPeer id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg view (Peers.getPeer_current id w v p a b run).1

theorem modify_device (f : Device → Device) (same : ∀ d, (f d).txSkbs = d.txSkbs) :
    SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  funext id
  simp [view,txPackets,Option.bind_map,Function.comp_def,same]

theorem set_tx (id : SkbId) (f : DataPacket → DataPacket)
    (same : ∀ p, material (f p) = material p) : SameView view (setTxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases device : w.dev with
  | none => simp [setTxSkb,liftSkb_run,device] at run
  | some d =>
    cases packet : d.txSkbs[id]? with
    | none =>
      simp [setTxSkb,liftSkb_run,SkbStore.setTx,SkbStore.getTx,device,packet,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      rw [Packets.setTxSkb_run w a d id p f device packet] at run
      cases run
      funext other
      by_cases eq : id = other
      · subst other
        simp [view,txPackets,Packets.update,device,packet,same]
      · simp [view,txPackets,Packets.update,device,Std.TreeMap.getElem?_insert,eq]

theorem publish (item : List SkbId) (state : PacketState) : SameView view (enqueuePerPeerTx item state) := by
  intro initial
  let P := fun w => view w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have read (id : SkbId) := (read_tx id).wp (fun v => v = initial)
  have peer (pid : PeerId) := (read_peer pid).wp (fun v => v = initial)
  have acquire (pid : PeerId) := (of_packets (peerGet_packets pid)).wp (fun v => v = initial)
  have release (pid : Option PeerId) := (of_packets (peerPut_packets pid)).wp (fun v => v = initial)
  have owner (who : IndexOwner) := indexOwner_peerDeref_preserves who P
  have write (id : SkbId) (state : PacketState) :=
    (set_tx id (fun p => {p with state := state}) (fun _ => rfl)).wp (fun v => v = initial)
  have cpu (seed : Nat) := (of_packets (cpu_packets seed)).wp (fun v => v = initial)
  have edit (f : Device → Device) (same : ∀ d, (f d).txSkbs = d.txSkbs) :=
    (modify_device f same).wp (fun v => v = initial)
  have getter : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  change Preserves P _
  unfold enqueuePerPeerTx
  cases head : item.head? with
  | none => exact ambient (AmbientM.invariant _)
  | some first =>
    simp only
    repeat' first
      | (allocation_release_head getTxSkb; exact read _)
      | (allocation_release_head getPeer; exact peer _)
      | (allocation_release_head IndexOwner.peerDeref; exact owner _)
      | (allocation_release_head peerGet; exact acquire _)
      | (allocation_release_head peerPut; exact release _)
      | (allocation_release_head setTxSkb; exact write _ _)
      | (allocation_release_head cpumaskChooseOnline; exact cpu _)
      | (allocation_release_head modifyDev; exact edit _ (fun _ => rfl))
      | (allocation_release_head getDev; unfold getDev)
      | (allocation_release_head branch; exact ambient (AmbientM.branch _ _))
      | (allocation_release_head invariant; exact ambient (AmbientM.invariant _))
      | (allocation_release_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
      | (allocation_release_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
      | (allocation_release_head queueDeviceWork; exact ambient (AmbientM.queueDeviceWork _))
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | allocation_release_step
    all_goals exact getter



theorem encrypt_packet (key : KeypairId) (pkt : DataPacket) :
    SameView (fun w : World => view w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  intro initial
  let P := fun w : World => view w.wg = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (fun w => view w = initial))
  have checksumSpec (p : Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) := by
    apply PublicationPoll.native_product (fun w => view w = initial) (getKeypair key)
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi hr
    exact (KeyTimes.getKeypair_return key w v k a b hr).1 ▸ hi
  change Preserves P _
  routing_tx_source [encryptPacket] using [padding,checksumSpec,keySpec,ambient]

/-- All packet iterations and the original DEAD/CRYPTED publication preserve
selected packet material; this includes a partial batch before encryption failure. -/
theorem encrypt_tail (item : Option (List SkbId)) :
    SameView (fun w : World => view w.wg) (RxWorkers.encryptStepTailSource item) := by
  intro initial
  let P := fun w : World => view w.wg = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product _ _ ((read_tx id).wp (fun v => v = initial))
  have write (id : SkbId) (bytes : List UInt8) :
      Preserves P (monadLift (setTxSkb id (fun p => {p with bytes := bytes})) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _
      ((set_tx id (fun p => {p with bytes := bytes}) (fun _ => rfl)).wp (fun v => v = initial))
  have publication (xs : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ ((publish xs state).wp (fun v => v = initial))
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := (encrypt_packet key pkt).wp (fun v => v = initial)
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publication,ambient]

end Leanux.Proofs.WG.TransmitSecurity.PacketMaterial
