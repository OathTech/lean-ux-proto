import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrames
import Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption

/-! The native encryption worker carries allocation provenance to its actual
packet reads and AEAD receipts, including receipts before later failure. The
incoming allocation carrier is explicit until initialized transport closes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open WorkerEncryption
set_option maxHeartbeats 600000
variable {id : SkbId}

def ReadOrigin (bank : List Journal.Event) (id : SkbId) (r : RunWitness DataPacket) : Prop :=
  ∃ generation, epoch r.before.wg = some generation ∧
    Certificate bank generation id (PacketMaterial.material r.value)

def Good (bank : List Journal.Event) (history : List WorkerEncryption.Receipt) : Prop :=
  ∀ r ∈ history, r.Valid ∧ ReadOrigin bank r.id r.read

def WorkerInv (bank : List Journal.Event) (h : List WorkerEncryption.Receipt) (w : World) : Prop :=
  Inv bank w.wg ∧ Good bank h

theorem read_origin (before : Inv bank r.before.wg)
    (valid : r.Valid (liftWG (getTxSkb id))) : ReadOrigin bank id r := by
  change (liftWG (getTxSkb id)).run r.before = .ok (r.value,r.after) at valid
  rw [liftWG_run] at valid
  cases native : ((getTxSkb id).run r.before.wg).run r.before.ambient with
  | error stop => simp [native,Except.map] at valid
  | ok out =>
    obtain ⟨⟨packet,w⟩,a⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    obtain ⟨same,_⟩ := valid
    obtain ⟨_,_,d,device,resident⟩ := Packets.getTxSkb_current id r.before.wg w packet r.before.ambient a native
    have found : TxDisposition.txPackets r.before.wg id = some r.value := by
      simp [TxDisposition.txPackets,device,resident,same]
    have atEpoch : epoch r.before.wg = some d.ifindex := by simp [epoch,device]
    exact ⟨d.ifindex,atEpoch,before d.ifindex atEpoch id r.value found⟩

private theorem lift_safe (a : Leanux.M α)
    (frame : Preserves (fun w : World => Inv bank w.wg) a) :
    PrefixPreserves (WorkerInv bank) (Good bank) (liftPrefix a) := by
  apply PrefixEnsures.lift
  · intro _ _ hi; exact hi.2
  · intro h w x v hi run
    exact ⟨(hoare_iff_run _ _ _).mp frame w x v hi.1 run,hi.2⟩

private theorem capture_safe (id : SkbId) :
    PrefixEnsures (WorkerInv bank) (Good bank) (captureRun (liftWG (getTxSkb id)))
      (fun r h w => WorkerInv bank h w ∧ r.Valid (liftWG (getTxSkb id)) ∧ ReadOrigin bank id r) := by
  apply PrefixEnsures.captureRun
  · intro _ _ hi; exact hi.2
  · intro h w packet v hi run
    have origin := read_origin hi.1 (r := ⟨packet,w,v⟩) run
    have frame : Preserves (fun w : World => Inv bank w.wg) (liftWG (getTxSkb id)) := by
      apply PublicationPoll.native_product
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a packet v b before run
      exact (Packets.getTxSkb_current id w v packet a b run).1 ▸ before
    exact ⟨⟨(hoare_iff_run _ _ _).mp frame w packet v hi.1 run,hi.2⟩,run,origin⟩

theorem crypt_safe (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (read : RunWitness DataPacket) (hh : head.Valid (liftWG (getTxSkb headId)))
    (hr : read.Valid (liftWG (getTxSkb id))) (origin : ReadOrigin bank id read) :
    PrefixPreserves (WorkerInv bank) (Good bank) (WorkerEncryption.crypt headId head id read) := by
  intro w h hi
  obtain ⟨suffix,eq,_,valid⟩ := Encryption.observe_receipts Env.checksumHelp head.value.keypair read.value w
    (h.filterMap (fun r => some r.cipher))
  have out := focusPrefix_suffix (fun r => (⟨headId,head,id,read,r⟩ : WorkerEncryption.Receipt))
    (fun r => some r.cipher) _ w h _ suffix (Prod.ext rfl eq)
  change runPrefix (WorkerEncryption.crypt headId head id read) w h = _ at out
  have good : Good bank (h ++ suffix.map (fun r => ⟨headId,head,id,read,r⟩)) := by
    intro r member
    rcases List.mem_append.mp member with old | fresh
    · exact hi.2 r old
    · obtain ⟨cipher,inside,rfl⟩ := List.mem_map.mp fresh
      exact ⟨⟨hh,hr,valid cipher inside⟩,origin⟩
  have erased := WorkerEncryption.crypt_erases headId head id read w h
  rw [out] at erased ⊢
  refine ⟨suffix.map (fun r => ⟨headId,head,id,read,r⟩),rfl,good,?_⟩
  cases result : (runPrefix (Encryption.observe Env.checksumHelp head.value.keypair read.value) w
      (h.filterMap (fun r => some r.cipher))).1 with
  | error stop => trivial
  | ok value =>
    have native := erased.symm.trans result
    exact ⟨(hoare_iff_run _ _ _).mp (encrypt_packet head.value.keypair read.value)
      w value.1 value.2 hi.1 native,good⟩

theorem packet_safe (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (hh : head.Valid (liftWG (getTxSkb headId))) :
    PrefixPreserves (WorkerInv bank) (Good bank) (WorkerEncryption.packet headId head id) := by
  unfold WorkerEncryption.packet
  apply PrefixEnsures.bind (capture_safe id)
  intro read w h hi
  exact crypt_safe headId head id read hh hi.2.1 hi.2.2 w h hi.1

private theorem ambient_safe (a : AmbientM α) :
    PrefixPreserves (WorkerInv bank) (Good bank) (liftPrefix (monadLift a : Leanux.M α)) :=
  lift_safe _ (productAmbient_spec a _ (fun _ _ hi => hi))

private theorem write_safe (id : SkbId) (bytes : List UInt8) :
    PrefixPreserves (WorkerInv bank) (Good bank)
      (liftPrefix (liftWG (setTxSkb id (fun p => {p with bytes})))) :=
  lift_safe _ (PublicationPoll.native_product _ _ (write_bytes id bytes))

private theorem publish_safe (items : List SkbId) (state : PacketState) :
    PrefixPreserves (WorkerInv bank) (Good bank)
      (liftPrefix (liftWG (enqueuePerPeerTx items state))) :=
  lift_safe _ (PublicationPoll.native_product _ _ (publish items state))

macro "origin_worker_step" : tactic => `(tactic| first
  | (nonce_product_head liftPrefix; with_reducible exact ambient_safe _)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.2))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem afterHead_safe (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket)
    (hh : head.Valid (liftWG (getTxSkb headId))) :
    PrefixPreserves (WorkerInv bank) (Good bank) (WorkerEncryption.afterHead first headId head) := by
  unfold WorkerEncryption.afterHead
  repeat' first
    | (nonce_product_head WorkerEncryption.packet; exact packet_safe _ _ _ hh)
    | with_reducible exact write_safe _ _
    | with_reducible exact publish_safe _ _
    | origin_worker_step
  all_goals exact ambient_safe (AmbientM.branch _ _)

theorem tail_safe (item : Option (List SkbId)) :
    PrefixPreserves (WorkerInv bank) (Good bank) (WorkerEncryption.tail item) := by
  unfold WorkerEncryption.tail
  apply PrefixPreserves.bind (ambient_safe _)
  intro _
  cases item with
  | none => exact PrefixPreserves.pure (fun _ _ hi => hi.2) _
  | some first =>
    dsimp only
    cases selected : first.head? with
    | none => exact ambient_safe _
    | some headId =>
      simp only
      apply PrefixEnsures.bind (capture_safe headId)
      intro head w h hi
      exact afterHead_safe first headId head hi.2.1 w h hi.1

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
