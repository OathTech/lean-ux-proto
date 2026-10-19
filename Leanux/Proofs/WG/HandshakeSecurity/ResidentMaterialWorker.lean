import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialWorkerEntry
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialWorkerFrames

/-! Actual encryption-worker transport of allocation-stamped sending
material. Histories retain every completed AEAD receipt before a later Stop.
Batch key homogeneity is a separate source property, not assumed silently. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity
set_option maxHeartbeats 600000

def Good (bank : List Journal.Event) (history : List WorkerEncryption.Receipt) : Prop :=
  ∀ r ∈ history, r.Valid ∧ (r.cipher.slot = r.read.value.keypair → BoundReceipt bank r)

def WorkerInv (bank : List Journal.Event) (h : List WorkerEncryption.Receipt) (w : World) : Prop :=
  Inv bank w.wg ∧ Good bank h

theorem cipher_append (slot : KeypairId) (packet : DataPacket) (w : World)
    (h : List Encryption.Receipt) :
    runPrefix (Encryption.observe Env.checksumHelp slot packet) w h =
      ((runPrefix (Encryption.observe Env.checksumHelp slot packet) w []).1,
        h ++ (runPrefix (Encryption.observe Env.checksumHelp slot packet) w []).2) := by
  rw [Encryption.observe_run,Encryption.observe_run]
  cases prepare : (Encryption.prepare Env.checksumHelp packet).run w with
  | error stop => simp
  | ok out =>
    obtain ⟨prepared,u⟩ := out
    cases prepared with
    | none => simp
    | some p =>
      cases key : (liftWG (getKeypair slot)).run u with
      | error stop => simp [key]
      | ok out =>
        obtain ⟨k,v⟩ := out
        cases checked : (branch .encSgvecFailed false : Leanux.M Bool).run v with
        | error stop => simp [key,checked]
        | ok out =>
          obtain ⟨failed,z⟩ := out
          cases failed <;> simp [key,checked]

theorem crypt_append (headId : SkbId) (head : RunWitness DataPacket)
    (id : SkbId) (read : RunWitness DataPacket) (w : World) (h : List WorkerEncryption.Receipt) :
    runPrefix (WorkerEncryption.crypt headId head id read) w h =
      ((runPrefix (WorkerEncryption.crypt headId head id read) w []).1,
        h ++ (runPrefix (WorkerEncryption.crypt headId head id read) w []).2) := by
  have source := cipher_append head.value.keypair read.value w (h.filterMap (fun r => some r.cipher))
  have focused := focusPrefix_suffix
    (fun cipher => (⟨headId,head,id,read,cipher⟩ : WorkerEncryption.Receipt))
    (fun r => some r.cipher) _ w h _ _ source
  exact focused

private theorem lift_safe (a : Leanux.M α)
    (frame : Preserves (fun w : World => Inv bank w.wg) a) :
    PrefixPreserves (WorkerInv bank) (Good bank) (liftPrefix a) := by
  apply PrefixEnsures.lift
  · intro _ _ hi; exact hi.2
  · intro h w x v hi run
    exact ⟨(hoare_iff_run _ _ _).mp frame w x v hi.1 run,hi.2⟩

private theorem capture_safe (id : SkbId) :
    PrefixEnsures (WorkerInv bank) (Good bank) (captureRun (liftWG (getTxSkb id)))
      (fun r h w => WorkerInv bank h w ∧ r.Valid (liftWG (getTxSkb id)) ∧
        Inv bank r.before.wg ∧ r.after = w) := by
  apply PrefixEnsures.captureRun
  · intro _ _ hi; exact hi.2
  · intro h w packet v hi run
    have same := (read_packet id (⟨packet,w,v⟩ : RunWitness DataPacket) run).1
    exact ⟨⟨same ▸ hi.1,hi.2⟩,run,hi.1,rfl⟩

theorem crypt_safe (headId : SkbId) (head : RunWitness DataPacket)
    (id : SkbId) (read : RunWitness DataPacket)
    (headValid : head.Valid (liftWG (getTxSkb headId))) :
    PrefixEnsures
      (fun h w => WorkerInv bank h w ∧ read.Valid (liftWG (getTxSkb id)) ∧
        Inv bank read.before.wg ∧ read.after = w)
      (Good bank) (WorkerEncryption.crypt headId head id read) (fun _ => WorkerInv bank) := by
  intro w h hi
  let fresh := runPrefix (WorkerEncryption.crypt headId head id read) w []
  have out := crypt_append headId head id read w h
  change runPrefix (WorkerEncryption.crypt headId head id read) w h = (fresh.1,h ++ fresh.2) at out
  have receipts := (WorkerEncryption.crypt_safe headId head id read headValid hi.2.1 w []
    (by intro r member; cases member)).choose_spec.2.1
  have bindings := crypt_bindings headId head id read w hi.2.2.1 hi.2.1 hi.2.2.2
  have good : Good bank (h ++ fresh.2) := by
    intro r member
    rcases List.mem_append.mp member with old | added
    · exact hi.1.2 r old
    · exact ⟨receipts r added,bindings r added⟩
  have erased := WorkerEncryption.crypt_erases headId head id read w h
  rw [out] at erased ⊢
  refine ⟨fresh.2,rfl,good,?_⟩
  cases result : fresh.1 with
  | error stop => trivial
  | ok value =>
    have native := erased.symm.trans result
    exact ⟨(hoare_iff_run _ _ _).mp (encrypt_packet head.value.keypair read.value)
      w value.1 value.2 hi.1.1 native,good⟩

theorem packet_safe (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (headValid : head.Valid (liftWG (getTxSkb headId))) :
    PrefixPreserves (WorkerInv bank) (Good bank) (WorkerEncryption.packet headId head id) := by
  unfold WorkerEncryption.packet
  exact PrefixEnsures.bind (capture_safe id) (fun read => crypt_safe headId head id read headValid)

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

macro "material_worker_step" : tactic => `(tactic| first
  | (nonce_product_head liftPrefix; with_reducible exact ambient_safe _)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.2))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem afterHead_safe (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket)
    (headValid : head.Valid (liftWG (getTxSkb headId))) :
    PrefixPreserves (WorkerInv bank) (Good bank) (WorkerEncryption.afterHead first headId head) := by
  unfold WorkerEncryption.afterHead
  repeat' first
    | (nonce_product_head WorkerEncryption.packet; exact packet_safe _ _ _ headValid)
    | with_reducible exact write_safe _ _
    | with_reducible exact publish_safe _ _
    | material_worker_step
  all_goals exact ambient_safe (AmbientM.branch _ _)

/-- Every actual worker AEAD receipt is tied to the packet's allocation-time
key core when the selected batch uses that packet's own key. The incoming
resident-material carrier remains explicit until initialized transport. -/
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

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
