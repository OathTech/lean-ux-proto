import Leanux.Proofs.WG.TransmitSecurity.WorkerEpochFrames
import Leanux.Proofs.WG.TransmitSecurity.WorkerOccurrences

/-! The exact native encryption worker keeps one device epoch at every
recorded packet read. The retained incoming journal may contain other epochs. -/
namespace Leanux.Proofs.WG.TransmitSecurity.WorkerEpochs
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open WorkerEncryption
set_option maxHeartbeats 600000

def Safe (generation : Option Nat) (bank history : List Receipt) : Prop :=
  ∃ suffix, history = bank ++ suffix ∧
    ∀ r ∈ suffix, PacketOrigins.epoch r.read.before.wg = generation

def Inv (generation : Option Nat) (bank h : List Receipt) (w : World) : Prop :=
  PacketOrigins.epoch w.wg = generation ∧ Safe generation bank h

theorem Safe.append (before : Safe generation bank h)
    (new : ∀ r ∈ suffix, PacketOrigins.epoch r.read.before.wg = generation) :
    Safe generation bank (h ++ suffix) := by
  obtain ⟨old,equal,good⟩ := before
  refine ⟨old ++ suffix,by rw [equal,List.append_assoc],?_⟩
  intro r member
  rcases List.mem_append.mp member with old | fresh
  · exact good r old
  · exact new r fresh

private theorem lift_safe (a : Leanux.M α)
    (frame : SameView (fun w : World => PacketOrigins.epoch w.wg) a) :
    PrefixPreserves (Inv generation bank) (Safe generation bank) (liftPrefix a) := by
  apply PrefixEnsures.lift
  · intro _ _ hi; exact hi.2
  · intro h w x v hi run
    exact ⟨((ProjectedAction.iff_run _ _ _).mp frame w x v run).trans hi.1,hi.2⟩

private theorem capture_safe (id : SkbId) :
    PrefixEnsures (Inv generation bank) (Safe generation bank) (captureRun (liftWG (getTxSkb id)))
      (fun r h w => Inv generation bank h w ∧ PacketOrigins.epoch r.before.wg = generation) := by
  apply PrefixEnsures.captureRun
  · intro _ _ hi; exact hi.2
  · intro h w packet v hi run
    exact ⟨⟨((ProjectedAction.iff_run _ _ _).mp (read_epoch id) w packet v run).trans hi.1,hi.2⟩,hi.1⟩

theorem crypt_safe (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (read : RunWitness DataPacket) (atEpoch : PacketOrigins.epoch read.before.wg = generation) :
    PrefixPreserves (Inv generation bank) (Safe generation bank) (WorkerEncryption.crypt headId head id read) := by
  intro w h hi
  obtain ⟨suffix,equal,_,_⟩ := Encryption.observe_receipts Env.checksumHelp head.value.keypair read.value w
    (h.filterMap (fun r => some r.cipher))
  have out := focusPrefix_suffix (fun r => (⟨headId,head,id,read,r⟩ : Receipt))
    (fun r => some r.cipher) _ w h _ suffix (Prod.ext rfl equal)
  change runPrefix (WorkerEncryption.crypt headId head id read) w h = _ at out
  have safe : Safe generation bank (h ++ suffix.map (fun r => ⟨headId,head,id,read,r⟩)) := by
    apply hi.2.append
    intro r member
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp member
    exact atEpoch
  have erased := WorkerEncryption.crypt_erases headId head id read w h
  rw [out] at erased ⊢
  refine ⟨suffix.map (fun r => ⟨headId,head,id,read,r⟩),rfl,safe,?_⟩
  cases result : (runPrefix (Encryption.observe Env.checksumHelp head.value.keypair read.value) w
      (h.filterMap (fun r => some r.cipher))).1 with
  | error stop => trivial
  | ok value =>
    have native := erased.symm.trans result
    exact ⟨((ProjectedAction.iff_run _ _ _).mp
      (PacketOrigins.encrypt_packet_epoch head.value.keypair read.value) w value.1 value.2 native).trans hi.1,safe⟩

theorem packet_safe (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId) :
    PrefixPreserves (Inv generation bank) (Safe generation bank) (WorkerEncryption.packet headId head id) := by
  unfold WorkerEncryption.packet
  apply PrefixEnsures.bind (capture_safe id)
  intro read w h hi
  exact crypt_safe headId head id read hi.2 w h hi.1

private theorem ambient_safe (a : AmbientM α) :
    PrefixPreserves (Inv generation bank) (Safe generation bank) (liftPrefix (monadLift a : Leanux.M α)) :=
by
  apply lift_safe
  intro initial
  exact productAmbient_spec a (fun w : World => PacketOrigins.epoch w.wg = initial) (fun _ _ hi => hi)

private theorem write_safe (id : SkbId) (bytes : List UInt8) :
    PrefixPreserves (Inv generation bank) (Safe generation bank)
      (liftPrefix (liftWG (setTxSkb id (fun p => {p with bytes})))) :=
  lift_safe _ (sameView_liftWG _ PacketOrigins.epoch _ (PacketOrigins.skb_epoch _) (fun _ _ _ hi => hi))

private theorem publish_safe (items : List SkbId) (state : PacketState) :
    PrefixPreserves (Inv generation bank) (Safe generation bank)
      (liftPrefix (liftWG (enqueuePerPeerTx items state))) :=
  lift_safe _ (sameView_liftWG _ PacketOrigins.epoch _
    (PacketOrigins.epoch_ring (TxRing.enqueuePeer_frame items state)) (fun _ _ _ hi => hi))

macro "worker_epoch_step" : tactic => `(tactic| first
  | (nonce_product_head liftPrefix; with_reducible exact ambient_safe _)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.2))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem afterHead_safe (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket) :
    PrefixPreserves (Inv generation bank) (Safe generation bank) (WorkerEncryption.afterHead first headId head) := by
  unfold WorkerEncryption.afterHead
  repeat' first
    | (nonce_product_head WorkerEncryption.packet; exact packet_safe _ _ _)
    | with_reducible exact write_safe _ _
    | with_reducible exact publish_safe _ _
    | worker_epoch_step
  all_goals exact ambient_safe (AmbientM.branch _ _)

theorem tail_safe (item : Option (List SkbId)) :
    PrefixPreserves (Inv generation bank) (Safe generation bank) (WorkerEncryption.tail item) := by
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
      exact afterHead_safe first headId head w h hi.1

/-- Packet identities in the new AEAD suffix are a sublist of the selected
IDs at this invocation's device epoch, independently of earlier journal epochs. -/
theorem tail_suffix (item : Option (List SkbId)) (w : World) (h : List Receipt) :
    ∃ suffix, (runPrefix (WorkerEncryption.tail item) w h).2 = h ++ suffix ∧
      (suffix.map Receipt.id).Sublist (item.getD []) ∧
      ∀ r ∈ suffix, PacketOrigins.epoch r.read.before.wg = PacketOrigins.epoch w.wg := by
  obtain ⟨suffix,equal,sub⟩ := WorkerEncryption.tail_footprint item w h
  have before : Inv (PacketOrigins.epoch w.wg) h h w :=
    ⟨rfl,[],by simp,by intro r member; cases member⟩
  obtain ⟨_,_,checked,_⟩ := tail_safe item w h before
  obtain ⟨other,same,good⟩ := checked
  have identical : suffix = other := List.append_cancel_left (equal.symm.trans same)
  exact ⟨suffix,equal,sub,identical.symm ▸ good⟩

def identity (r : Receipt) : Option Nat × SkbId := (PacketOrigins.epoch r.read.before.wg,r.id)

/-- A native selected worker cannot repeat any old identity when its pending
IDs are disjoint from prior encryptions, and cannot repeat within its new
suffix when selection IDs are distinct. Stops retain the same guarantee. -/
theorem tail_nonreuse (item : Option (List SkbId)) (w : World) (h : List Receipt)
    (old : (h.map identity).Nodup) (unique : (item.getD []).Nodup)
    (separate : ∀ id ∈ item.getD [], (PacketOrigins.epoch w.wg,id) ∉ h.map identity) :
    ((runPrefix (WorkerEncryption.tail item) w h).2.map identity).Nodup := by
  obtain ⟨suffix,equal,sub,epochs⟩ := tail_suffix item w h
  have same : suffix.map identity = (suffix.map Receipt.id).map (fun id => (PacketOrigins.epoch w.wg,id)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r member
    exact Prod.ext (epochs r member) rfl
  have fresh : (suffix.map identity).Nodup := by
    rw [same]
    exact (unique.sublist sub).map (fun id => (PacketOrigins.epoch w.wg,id)) (fun _ _ different equal => different (congrArg Prod.snd equal))
  rw [equal,List.map_append]
  apply List.nodup_append.mpr
  refine ⟨old,fresh,?_⟩
  intro earlier present later member eq
  obtain ⟨r,inside,rfl⟩ := List.mem_map.mp member
  have idMember : r.id ∈ item.getD [] := sub.subset (List.mem_map.mpr ⟨r,inside,rfl⟩)
  apply separate r.id idMember
  have label : identity r = (PacketOrigins.epoch w.wg,r.id) := Prod.ext (epochs r inside) rfl
  exact label ▸ eq ▸ present

end Leanux.Proofs.WG.TransmitSecurity.WorkerEpochs
