import Leanux.Proofs.WG.Queues.TxMarkTransport
import Leanux.Proofs.WG.Queues.HolderEncryptHistory

/-! The existing encryption continuation acts on the item already selected
before the actual softirq. This frame starts after that callback; it does not
replace it or infer item separation from a later ring state. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.SelectedEncrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem lift_native (target : SkbId) {action : WG.M α}
    (frame : SameView (fun w=>txPackets w target) action) :
    SameView (fun w : World=>txPackets w.wg target) (liftWG action) :=
  sameView_liftWG _ _ action frame (fun _ _ _ same=>same)

private theorem read_packet (target id : SkbId) :
    SameView (fun w : World=>txPackets w.wg target) (liftWG (getTxSkb id)) :=
  lift_native target
    ((pinned_const _private.Leanux.Proofs.WG.Queues.TxMarkTransport.«0».Leanux.Proofs.WG.Queues.TxDisposition.MarkTransport.readPacket) target id)

/-- Concrete checksum help and all encryption failure arms leave packet
store cells unchanged; encryption bytes are installed by the later setter. -/
theorem packet_other (target : SkbId) (key : KeypairId) (pkt : DataPacket) :
    SameView (fun w : World=>txPackets w.wg target) (encryptPacket Env.checksumHelp key pkt) := by
  intro initial
  let P := fun w : World=>txPackets w.wg target=initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  have padding : Preserves P (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    (lift_native target ((calculateSkbPadding_sameWGWorld _ _).factor (fun w=>txPackets w target))).wp (·=initial)
  have checksum (p : WG.Packet) : Preserves P (Env.checksumHelp p) := (checksumHelp_sameWorld p).wp P
  have keyFrame : SameView (fun w=>txPackets w target) (getKeypair key) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    exact congrArg (fun w=>txPackets w target) (KeyTimes.getKeypair_return key w v value a b run).1
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) := (lift_native target keyFrame).wp (·=initial)
  change Preserves P _
  routing_tx_source [encryptPacket] using [padding,checksum,keySpec,ambient]

private theorem loop {β : Type} (items : List SkbId) (initial : β)
    (body : SkbId→β→Leanux.M (ForInStep β)) (P : World→Prop)
    (step : ∀ id∈items,∀ state,Preserves P (body id state)) :
    Preserves P (forIn items initial body) := by
  induction items generalizing initial with
  | nil=>simpa only [List.forIn_nil] using (preserves_pure initial : Preserves P (pure initial : Leanux.M β))
  | cons id ids ih=>
    rw [List.forIn_cons]
    apply preserves_bind (step id (by simp) initial)
    intro result
    cases result with
    | done value=>exact preserves_pure value
    | yield value=>exact ih value (fun next member=>step next (by simp [member]))

/-- This is the original selected encryption step after the ring consume and
softirq, with its exact concrete checksum callback. It may stop at any source
guard; normal return retains every packet outside the saved selected item. -/
theorem step_other (target : SkbId) (item : List SkbId) (outside : target∉item) :
    SameView (fun w : World=>txPackets w.wg target)
      (RxWorkers.encryptStepTailSource (some item)) := by
  intro initial
  let P := fun w : World=>txPackets w.wg target=initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (liftAmbient a) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  have getter := fun id=>(read_packet target id).wp (·=initial)
  have setter (id : SkbId) (member : id∈item) (f : DataPacket→DataPacket) :
      Preserves P (liftWG (setTxSkb id f)) :=
    (lift_native target (MarkTransport.set_other target id (fun same=>outside (same ▸ member)) f)).wp (·=initial)
  have publish (state : PacketState) : Preserves P (liftWG (enqueuePerPeerTx item state)) :=
    (lift_native target (MarkTransport.publish_other target item state outside)).wp (·=initial)
  change Preserves P _
  unfold RxWorkers.encryptStepTailSource
  apply preserves_bind (ambient (AmbientM.branch .encWorkerConsumed true))
  intro _
  dsimp only
  cases head:item.head? with
  | none=>exact ambient (AmbientM.invariant _)
  | some headId=>
    dsimp only
    apply preserves_bind (getter headId)
    intro saved
    apply preserves_bind
    · apply loop item _ _ P
      intro id member state
      apply preserves_bind (ambient (AmbientM.branch .encWorkerSkbIterate true))
      intro _
      apply preserves_bind (getter id)
      intro packet
      apply preserves_bind ((packet_other target saved.keypair packet).wp (·=initial))
      intro encrypted
      apply preserves_bind (ambient (AmbientM.branch .encWorkerEncrypted encrypted.isSome))
      intro success
      split
      · exact preserves_bind (setter id member _) (fun _=>preserves_pure _)
      · exact preserves_pure _
    · intro state
      split
      · exact preserves_bind (ambient (AmbientM.branch .encWorkerSkbIterate false))
          (fun _=>preserves_bind (publish state) (fun _=>preserves_pure _))
      · exact preserves_bind (publish state) (fun _=>preserves_pure _)

theorem step_head (target : SkbId) (item : List SkbId) (outside : target∉item) (state : PacketState) :
    Preserves (fun w : World=>HeadState target state w.wg)
      (RxWorkers.encryptStepTailSource (some item)) :=
  (step_other target item outside).wp (fun cell=>∃p,cell=some p ∧ p.state=state)

theorem tail_other (target : SkbId) (item : List SkbId) (outside : target∉item) :
    SameView (fun w : World=>txPackets w.wg target)
      (RxWorkers.encryptTailSource (some item)) := by
  intro initial
  let P := fun w : World=>txPackets w.wg target=initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (liftAmbient a) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  have stepSpec : Preserves P (RxWorkers.encryptStepTailSource (some item)) :=
    (step_other target item outside).wp (·=initial)
  have needSpec : Preserves P (Env.condResched .encryptWorker) :=
    ((condResched_sameKernel .encryptWorker).of_factor
      (fun s : ProductStore43=>txPackets {dev:=s.2.2.2.dev} target)
      (fun w=>txPackets w.wg target) (fun _=>rfl)).wp (·=initial)
  change Preserves P _
  unfold RxWorkers.encryptTailSource workerIter
  apply preserves_bind stepSpec
  intro more
  split
  · exact preserves_pure _
  · apply preserves_bind
    · exact preserves_bind needSpec (fun need=>ambient (AmbientM.branch .encWorkerNeedResched need))
    · intro yielded
      split <;> exact preserves_pure _

theorem tail_head (target : SkbId) (item : List SkbId) (outside : target∉item) (state : PacketState) :
    Preserves (fun w : World=>HeadState target state w.wg)
      (RxWorkers.encryptTailSource (some item)) :=
  (tail_other target item outside).wp (fun cell=>∃p,cell=some p ∧ p.state=state)

/-- The unchanged lifetime observer supplies this same selected source cut,
for every incoming journal. Only its actual normal endpoint is used. -/
theorem observed_head (target : SkbId) (item : List SkbId) (outside : target∉item) (state : PacketState)
    (head : HeadState target state w.wg)
    (run : runPrefix (RxHistory.mixed (RxWorkers.encryptTail (some item))) w history=(.ok (result,v),after)) :
    HeadState target state v.wg := by
  have actual := ((RxHistory.mixed_erases (RxWorkers.encryptTail_erases (some item))) w history).symm.trans
    (congrArg Prod.fst run)
  exact (hoare_iff_run _ _ _).mp (tail_head target item outside state) w result v head actual

end Leanux.Proofs.WG.Queues.TxDisposition.SelectedEncrypt
