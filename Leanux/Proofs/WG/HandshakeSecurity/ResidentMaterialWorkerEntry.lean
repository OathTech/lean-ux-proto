import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialAllocation
import Leanux.Proofs.WG.TransmitSecurity.EncryptBinding
import Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption

/-! Actual native packet and AEAD reads discharge the conditional material
obligation. Batch key homogeneity is kept visible here; its initialized
physical-queue proof is separate from key lifetime transport. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder TxDisposition

theorem read_packet (id : SkbId) (r : RunWitness DataPacket)
    (valid : r.Valid (liftWG (getTxSkb id))) :
    r.after.wg = r.before.wg ∧
      ∃ d, r.before.wg.dev = some d ∧ d.txSkbs[id]? = some r.value := by
  change (liftWG (getTxSkb id)).run r.before = .ok (r.value,r.after) at valid
  rw [liftWG_run] at valid
  cases native : ((getTxSkb id).run r.before.wg).run r.before.ambient with
  | error stop => simp [native,Except.map] at valid
  | ok out =>
    obtain ⟨⟨packet,w⟩,a⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    obtain ⟨same,state⟩ := valid
    obtain ⟨unchanged,_,d,device,resident⟩ :=
      Packets.getTxSkb_current id r.before.wg w packet r.before.ambient a native
    refine ⟨?_,d,device,by simpa only [same] using resident⟩
    have world := congrArg World.wg state
    exact world.symm.trans unchanged

/-- The native cipher key read supplies actual residency. Its allocation and
sending material therefore equal the key core captured at this packet's
actual allocation. No key-credit or forward-survival premise is required. -/
theorem cipher_binding (id : SkbId) (read : RunWitness DataPacket)
    (before : Inv bank read.before.wg) (readValid : read.Valid (liftWG (getTxSkb id)))
    (cipher : Encryption.Receipt) (cipherValid : cipher.Valid Env.checksumHelp)
    (start : cipher.preparation.before = read.after)
    (homogeneous : cipher.slot = read.value.keypair) :
    ∃ generation, PacketOrigins.epoch read.before.wg = some generation ∧
      Certificate bank generation id (PacketMaterial.material read.value)
        (keyCore cipher.keyRead.value) := by
  obtain ⟨same,d,device,resident⟩ := read_packet id read readValid
  obtain ⟨_,core,certificate,conditional⟩ := before d device id read.value resident
  have atEntry := cipher.entry_key cipherValid
  have coreResident : pool read.before.wg read.value.keypair = some (keyCore cipher.keyRead.value) := by
    have actual : (read.before.wg.dev.bind fun d => d.keypairs[read.value.keypair]?) =
        some cipher.keyRead.value := by
      simpa only [Encryption.keyAt,start,homogeneous,same] using atEntry
    simp only [Responder.pool,actual,Option.map_some]
  have coreSame := conditional _ coreResident
  exact ⟨d.ifindex,by simp [PacketOrigins.epoch,device],coreSame.symm ▸ certificate⟩

/-- Every AEAD receipt emitted by the native encryption observer starts at
the supplied world, including receipts retained in a later stopped worker. -/
theorem cipher_starts (slot : KeypairId) (packet : DataPacket) (w : World) :
    ∀ r ∈ (runPrefix (Encryption.observe Env.checksumHelp slot packet) w []).2,
      r.preparation.before = w := by
  rw [Encryption.observe_run]
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

def BoundReceipt (bank : List Journal.Event) (r : WorkerEncryption.Receipt) : Prop :=
  ∃ generation, PacketOrigins.epoch r.read.before.wg = some generation ∧
    Certificate bank generation r.id (PacketMaterial.material r.read.value)
      (keyCore r.cipher.keyRead.value)

/-- The exact worker crypt callback attaches allocation/material evidence to
each emitted AEAD receipt. Its supplied packet read must be the immediately
preceding native read; arbitrary independently erased executions do not join. -/
theorem crypt_bindings (headId : SkbId) (head : RunWitness DataPacket)
    (id : SkbId) (read : RunWitness DataPacket) (w : World)
    (before : Inv bank read.before.wg) (readValid : read.Valid (liftWG (getTxSkb id)))
    (entered : read.after = w) :
    ∀ r ∈ (runPrefix (WorkerEncryption.crypt headId head id read) w []).2,
      r.cipher.slot = r.read.value.keypair → BoundReceipt bank r := by
  intro r member homogeneous
  change r ∈ ((runPrefix (Encryption.observe Env.checksumHelp head.value.keypair read.value) w []).2.map
    (fun cipher => (⟨headId,head,id,read,cipher⟩ : WorkerEncryption.Receipt))) at member
  obtain ⟨cipher,inside,rfl⟩ := List.mem_map.mp member
  obtain ⟨suffix,equal,_,valid⟩ :=
    Encryption.observe_receipts Env.checksumHelp head.value.keypair read.value w []
  have insideSuffix : cipher ∈ suffix := by simpa only [equal,List.nil_append] using inside
  apply cipher_binding id read before readValid cipher (valid cipher insideSuffix).2.2
  · exact (cipher_starts head.value.keypair read.value w cipher inside).trans entered.symm
  · exact homogeneous

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
