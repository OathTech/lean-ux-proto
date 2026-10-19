import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginWrite

/-! Native encryption establishes a receipt certificate before the worker
writes the returned bytes. Existing resident certificates survive preparation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open WorkerEncryption TxDisposition
variable {id : SkbId}

abbrev WorkerInv (h : List WorkerEncryption.Receipt) (w : World) := Inv h w.wg

theorem encrypt_call (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (read : RunWitness DataPacket) (hh : head.Valid (liftWG (getTxSkb headId)))
    (hr : read.Valid (liftWG (getTxSkb id))) :
    PrefixEnsures (fun h w => WorkerInv h w ∧ read.after = w) (fun _ => True)
      (WorkerEncryption.crypt headId head id read)
      (fun output h w => WorkerInv h w ∧ ∀ bytes, output = some bytes → WriteSource h id bytes w.wg) := by
  intro w h before
  obtain ⟨suffix,extension⟩ := Appends.focus
    (fun r => (⟨headId,head,id,read,r⟩ : WorkerEncryption.Receipt))
    (fun r => some r.cipher) (Encryption.observe Env.checksumHelp head.value.keypair read.value) w h
  change (runPrefix (WorkerEncryption.crypt headId head id read) w h).2 = h ++ suffix at extension
  refine ⟨suffix,extension,True.intro,?_⟩
  cases result : (runPrefix (WorkerEncryption.crypt headId head id read) w h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨output,v⟩ := out
    have native := (WorkerEncryption.crypt_erases headId head id read w h).symm.trans result
    have retained := (hoare_iff_run _ _ _).mp (encrypt_packet head.value.keypair read.value)
      w output v before.1 native
    refine ⟨retained.mono (by intro r member; rw [extension]; exact List.mem_append_left _ member),?_⟩
    intro bytes same generation atEpoch packet resident
    subst output
    obtain ⟨cipher,source,slot,packetEq,valid,start,cipherBytes⟩ :=
      WorkerCiphertext.crypt_success headId head id read w v h bytes result
    have epochEq := (ProjectedAction.iff_run _ _ _).mp
      (encrypt_packet_epoch head.value.keypair read.value) w (some bytes) v native
    have payloadEq := (ProjectedAction.iff_run _ _ _).mp
      (PacketPayload.encrypt_packet head.value.keypair read.value) w (some bytes) v native
    obtain ⟨readWorld,readCell⟩ := read_cell read hr
    have readEpoch : PacketOrigins.epoch read.before.wg = some generation := by
      rw [← readWorld,before.2,← epochEq]
      exact atEpoch
    have readPayload : PacketPayload.material read.value = PacketPayload.material packet := by
      have stored : PacketPayload.view w.wg id = some (PacketPayload.material read.value) := by
        rw [← before.2]
        simp only [PacketPayload.view,readCell,Option.map_some]
      have current : PacketPayload.view v.wg id = some (PacketPayload.material packet) := by
        simp only [PacketPayload.view,resident,Option.map_some]
      rw [payloadEq,stored] at current
      exact Option.some.inj current
    rw [source]
    refine ⟨⟨headId,head,id,read,cipher⟩,by simp,⟨hh,hr,slot,packetEq,valid⟩,rfl,readEpoch,?_⟩
    have replaced := congrArg (fun p : DataPacket => {p with bytes := bytes}) readPayload
    simpa only [PacketPayload.material,cipherBytes] using replaced

private theorem capture (id : SkbId) :
    PrefixEnsures WorkerInv (fun _ => True) (captureRun (liftWG (getTxSkb id)))
      (fun r h w => WorkerInv h w ∧ r.Valid (liftWG (getTxSkb id)) ∧ r.after = w) := by
  apply PrefixEnsures.captureRun _ (fun _ _ _ => True.intro)
  intro h w packet v before run
  have same := (read_cell (id := id) ⟨packet,w,v⟩ run).1
  refine ⟨?_,run,rfl⟩
  change Inv h v.wg
  change v.wg = w.wg at same
  rw [same]
  exact before

theorem packet (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (hh : head.Valid (liftWG (getTxSkb headId))) :
    PrefixEnsures WorkerInv (fun _ => True) (WorkerEncryption.packet headId head id)
      (fun output h w => WorkerInv h w ∧ ∀ bytes, output = some bytes → WriteSource h id bytes w.wg) := by
  unfold WorkerEncryption.packet
  apply PrefixEnsures.bind (capture id)
  intro read w h before
  exact encrypt_call headId head id read hh before.2.1 w h ⟨before.1,before.2.2⟩

private theorem lift_safe (a : Leanux.M α)
    (frame : ∀ h, Preserves (fun w : World => Inv h w.wg) a) :
    PrefixPreserves WorkerInv (fun _ => True) (liftPrefix a) := by
  apply PrefixEnsures.lift _ (fun _ _ _ => True.intro)
  intro h w result v before run
  exact (hoare_iff_run _ _ _).mp (frame h) w result v before run

private theorem ambient (a : AmbientM α) :
    PrefixPreserves WorkerInv (fun _ => True) (liftPrefix (monadLift a : Leanux.M α)) :=
  lift_safe _ (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))

private theorem checked (output : Option (List UInt8)) :
    PrefixEnsures (fun h w => WorkerInv h w ∧
        ∀ bytes, output = some bytes → WriteSource h id bytes w.wg) (fun _ => True)
      (liftPrefix (branch .encWorkerEncrypted output.isSome))
      (fun yes h w => (WorkerInv h w ∧
        ∀ bytes, output = some bytes → WriteSource h id bytes w.wg) ∧ yes = output.isSome) := by
  apply PrefixEnsures.lift _ (fun _ _ _ => True.intro)
  intro h w result v before run
  cases run
  exact ⟨before,rfl⟩

private theorem write (id : SkbId) (bytes : List UInt8) :
    PrefixEnsures (fun h w => WorkerInv h w ∧ WriteSource h id bytes w.wg) (fun _ => True)
      (liftPrefix (liftWG (setTxSkb id (fun p => {p with bytes}))))
      (fun _ => WorkerInv) := by
  apply PrefixEnsures.lift _ (fun _ _ _ => True.intro)
  intro h w result v before run
  rw [liftWG_run] at run
  cases native : ((setTxSkb id (fun p => {p with bytes})).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at run
  | ok out =>
    obtain ⟨⟨value,g⟩,a⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨_,rfl⟩ := run
    exact (hoare_iff_run_ambient _ _ _).mp (write_bytes id bytes) w.wg w.ambient value g a before native

private theorem publication (items : List SkbId) (state : PacketState) :
    PrefixPreserves WorkerInv (fun _ => True)
      (liftPrefix (liftWG (enqueuePerPeerTx items state))) :=
  lift_safe _ (fun _ => PublicationPoll.native_product _ _ (CiphertextOrigins.publish items state))

theorem afterHead (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket)
    (hh : head.Valid (liftWG (getTxSkb headId))) :
    PrefixPreserves WorkerInv (fun _ => True) (WorkerEncryption.afterHead first headId head) := by
  unfold WorkerEncryption.afterHead
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ (fun _ _ _ => True.intro)
    intro id state
    apply PrefixPreserves.bind (ambient _)
    intro _
    apply PrefixEnsures.bind (packet headId head id hh)
    intro encrypted
    apply PrefixEnsures.bind (checked encrypted)
    intro yes w h before
    obtain ⟨kept,same⟩ := before
    subst yes
    cases encrypted with
    | none =>
      exact (PrefixPreserves.pure (I := WorkerInv) (fun _ _ _ => True.intro) _) w h kept.1
    | some bytes =>
      have rule : PrefixEnsures (fun h w => WorkerInv h w ∧ WriteSource h id bytes w.wg)
          (fun _ => True)
          (do liftPrefix (liftWG (setTxSkb id (fun p => {p with bytes})))
              pure (ForInStep.yield state)) (fun _ => WorkerInv) :=
        PrefixEnsures.bind (write id bytes)
          (fun _ => PrefixPreserves.pure (fun _ _ _ => True.intro) _)
      exact rule w h ⟨kept.1,kept.2 bytes rfl⟩
  · intro state
    dsimp only
    split
    · apply PrefixPreserves.bind (ambient _)
      intro _
      apply PrefixPreserves.bind (publication first state)
      intro _
      exact PrefixPreserves.pure (fun _ _ _ => True.intro) _
    · apply PrefixPreserves.bind (publication first state)
      intro _
      exact PrefixPreserves.pure (fun _ _ _ => True.intro) _

theorem tail (item : Option (List SkbId)) :
    PrefixPreserves WorkerInv (fun _ => True) (WorkerEncryption.tail item) := by
  unfold WorkerEncryption.tail
  apply PrefixPreserves.bind (ambient _)
  intro _
  cases item with
  | none => exact PrefixPreserves.pure (fun _ _ _ => True.intro) _
  | some first =>
    dsimp only
    cases selected : first.head? with
    | none => exact ambient _
    | some headId =>
      simp only
      apply PrefixEnsures.bind (capture headId)
      intro head w h before
      exact afterHead first headId head before.2.1 w h before.1

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
