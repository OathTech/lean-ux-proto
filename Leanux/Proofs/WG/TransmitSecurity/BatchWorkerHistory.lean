import Leanux.Proofs.WG.TransmitSecurity.BatchCoherenceFrames

/-! The selected worker appends head/packet agreement to an arbitrary safe
history, even when older receipts came from different peers and keys. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchWorkerHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open WorkerEncryption BatchCoherence
set_option maxHeartbeats 600000
variable {items : List SkbId} {pid : PeerId} {slot : KeypairId}

def Fields (pid : PeerId) (slot : KeypairId) (packet : DataPacket) : Prop :=
  packet.peer = pid ∧ packet.keypair = slot

def Good (h : List Receipt) : Prop :=
  ∀ r ∈ h, r.head.value.keypair = r.read.value.keypair ∧ r.head.value.peer = r.read.value.peer ∧
    r.cipher.slot = r.read.value.keypair

def Inv (pid : PeerId) (slot : KeypairId) (items : List SkbId)
    (h : List Receipt) (w : World) : Prop := Aligned w.wg pid slot items ∧ Good h

private theorem lift_safe (action : Leanux.M α)
    (frame : Preserves (fun w : World => Aligned w.wg pid slot items) action) :
    PrefixPreserves (Inv pid slot items) Good (liftPrefix action) := by
  apply PrefixEnsures.lift
  · intro _ _ hi; exact hi.2
  · intro h w result v hi run
    exact ⟨(hoare_iff_run _ _ _).mp frame w result v hi.1 run,hi.2⟩

private theorem capture (id : SkbId) (member : id ∈ items) :
    PrefixEnsures (Inv pid slot items) Good (captureRun (liftWG (getTxSkb id)))
      (fun r h w => Inv pid slot items h w ∧ Fields pid slot r.value) := by
  apply PrefixEnsures.captureRun
  · intro _ _ hi; exact hi.2
  · intro h w packet v before run
    rw [liftWG_run] at run
    cases native : ((getTxSkb id).run w.wg).run w.ambient with
    | error stop => simp [native,Except.map] at run
    | ok output =>
      obtain ⟨⟨value,g⟩,a⟩ := output
      simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      obtain ⟨same,_,d,device,resident⟩ := Packets.getTxSkb_current id w.wg g value w.ambient a native
      have found : TxDisposition.txPackets w.wg id = some value := by
        simp [TxDisposition.txPackets,device,resident]
      exact ⟨⟨same ▸ before.1,before.2⟩,before.1 id member value found⟩

theorem crypt (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (read : RunWitness DataPacket) (headFields : Fields pid slot head.value)
    (readFields : Fields pid slot read.value) :
    PrefixPreserves (Inv pid slot items) Good (WorkerEncryption.crypt headId head id read) := by
  intro w h before
  obtain ⟨suffix,equal,_,valid⟩ := Encryption.observe_receipts Env.checksumHelp head.value.keypair read.value w
    (h.filterMap (fun r => some r.cipher))
  have observed := focusPrefix_suffix (fun r => (⟨headId,head,id,read,r⟩ : Receipt))
    (fun r => some r.cipher) _ w h _ suffix (Prod.ext rfl equal)
  change runPrefix (WorkerEncryption.crypt headId head id read) w h = _ at observed
  have good : Good (h ++ suffix.map (fun r => ⟨headId,head,id,read,r⟩)) := by
    intro r member
    rcases List.mem_append.mp member with old | fresh
    · exact before.2 r old
    · obtain ⟨cipher,present,rfl⟩ := List.mem_map.mp fresh
      exact ⟨headFields.2.trans readFields.2.symm,headFields.1.trans readFields.1.symm,
        (valid cipher present).1.trans (headFields.2.trans readFields.2.symm)⟩
  have erased := WorkerEncryption.crypt_erases headId head id read w h
  rw [observed] at erased ⊢
  refine ⟨suffix.map (fun r => ⟨headId,head,id,read,r⟩),rfl,good,?_⟩
  cases result : (runPrefix (Encryption.observe Env.checksumHelp head.value.keypair read.value) w
      (h.filterMap (fun r => some r.cipher))).1 with
  | error stop => trivial
  | ok out =>
    exact ⟨(hoare_iff_run _ _ _).mp
      (product_aligned (PacketMaterial.encrypt_packet head.value.keypair read.value))
      w out.1 out.2 before.1 (erased.symm.trans result),good⟩

theorem packet (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (headFields : Fields pid slot head.value) (member : id ∈ items) :
    PrefixPreserves (Inv pid slot items) Good (WorkerEncryption.packet headId head id) := by
  unfold WorkerEncryption.packet
  apply PrefixEnsures.bind (capture id member)
  intro read w h before
  exact crypt headId head id read headFields before.2 w h before.1

private theorem loop (xs : List α) (init : β) (body : α → β → PrefixM Receipt (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, PrefixPreserves (Inv pid slot items) Good (body x b)) :
    PrefixPreserves (Inv pid slot items) Good (forIn xs init body) := by
  induction xs generalizing init with
  | nil => exact PrefixPreserves.pure (fun _ _ hi => hi.2) _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply PrefixPreserves.bind (step x (by simp) init)
    intro result
    cases result with
    | done value => exact PrefixPreserves.pure (fun _ _ hi => hi.2) _
    | yield value => exact ih value (fun y member => step y (by simp [member]))

private theorem ambient (action : AmbientM α) :
    PrefixPreserves (Inv pid slot items) Good (liftPrefix (monadLift action : Leanux.M α)) :=
  lift_safe _ (productAmbient_spec action _ (fun _ _ hi => hi))

private theorem write (id : SkbId) (bytes : List UInt8) :
    PrefixPreserves (Inv pid slot items) Good
      (liftPrefix (liftWG (setTxSkb id (fun p => {p with bytes})))) :=
  lift_safe _ (PublicationPoll.native_product _ _ (aligned (pid := pid) (slot := slot) (items := items)
    (PacketMaterial.set_tx id (fun p => {p with bytes}) (fun _ => rfl))))

private theorem publish (batch : List SkbId) (state : PacketState) :
    PrefixPreserves (Inv pid slot items) Good
      (liftPrefix (liftWG (enqueuePerPeerTx batch state))) :=
  lift_safe _ (PublicationPoll.native_product _ _ (aligned (PacketMaterial.publish batch state)))

macro "batch_history_step" : tactic => `(tactic| first
  | with_reducible exact write _ _
  | with_reducible exact publish _ _
  | (nonce_product_head liftPrefix; first
      | exact ambient (AmbientM.branch _ _)
      | with_reducible exact ambient _)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem afterHead (headId : SkbId) (head : RunWitness DataPacket)
    (headFields : Fields pid slot head.value) :
    PrefixPreserves (Inv pid slot items) Good (WorkerEncryption.afterHead items headId head) := by
  unfold WorkerEncryption.afterHead
  apply PrefixPreserves.bind
  · apply loop
    intro id member state
    repeat' first
      | (nonce_product_head WorkerEncryption.packet; exact packet headId head id headFields member)
      | batch_history_step
  · intro state
    repeat' batch_history_step

theorem tail : PrefixPreserves (Inv pid slot items) Good (WorkerEncryption.tail (some items)) := by
  unfold WorkerEncryption.tail
  apply PrefixPreserves.bind (ambient _)
  intro _
  dsimp only
  cases head : items.head? with
  | none => exact ambient _
  | some id =>
    simp only
    apply PrefixEnsures.bind (capture (items := items) id (List.mem_of_mem_head? (by simp [head])))
    intro read w h before
    exact afterHead id read before.2 w h before.1

end Leanux.Proofs.WG.TransmitSecurity.BatchWorkerHistory
