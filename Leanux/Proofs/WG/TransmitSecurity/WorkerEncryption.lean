import Leanux.Proofs.WG.TransmitSecurity.EncryptReceipts
import Leanux.Proofs.WG.Queues.RxWorkerCuts
import Leanux.Proofs.Logged.Focus
import Leanux.Proofs.WG.TransmitSecurity.NoncePoll

/-! Native encryption-worker packet selections attached to the actual AEAD
receipts. Both the batch head key word and each packet read are captured. -/
namespace Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

structure Receipt where
  headId : SkbId
  head : RunWitness DataPacket
  id : SkbId
  read : RunWitness DataPacket
  cipher : Encryption.Receipt

def Receipt.Valid (r : Receipt) : Prop :=
  r.head.Valid (liftWG (getTxSkb r.headId)) ∧
  r.read.Valid (liftWG (getTxSkb r.id)) ∧
  r.cipher.slot = r.head.value.keypair ∧ r.cipher.packet = r.read.value ∧
  r.cipher.Valid Env.checksumHelp

def Good (h : List Receipt) : Prop := ∀ r ∈ h, r.Valid

def crypt (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (read : RunWitness DataPacket) : PrefixM Receipt (Option (List UInt8)) :=
  focusPrefix (fun r => ⟨headId,head,id,read,r⟩) (fun r => some r.cipher)
    (Encryption.observe Env.checksumHelp head.value.keypair read.value)

def packet (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId) : PrefixM Receipt (Option (List UInt8)) := do
  let read ← captureRun (liftWG (getTxSkb id))
  crypt headId head id read

def afterHead (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket) : PrefixM Receipt Bool := do
  let mut state := PacketState.crypted
  for id in first do
    _ ← liftPrefix (branch .encWorkerSkbIterate true)
    let encrypted ← packet headId head id
    if ← liftPrefix (branch .encWorkerEncrypted encrypted.isSome) then
      liftPrefix (liftWG (setTxSkb id fun p => {p with bytes := encrypted.getD []}))
    else
      state := .dead
      break
  if state == .crypted then _ ← liftPrefix (branch .encWorkerSkbIterate false)
  liftPrefix (liftWG (enqueuePerPeerTx first state))
  return true

def tail (item : Option (List SkbId)) : PrefixM Receipt Bool := do
  _ ← liftPrefix (branch .encWorkerConsumed item.isSome)
  match item with
  | none => return false
  | some first =>
    let some headId := first.head? | liftPrefix (invariant "an empty ring item")
    let head ← captureRun (liftWG (getTxSkb headId))
    afterHead first headId head

theorem crypt_erases (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (read : RunWitness DataPacket) :
    ErasesPrefix (crypt headId head id read) (encryptPacket Env.checksumHelp head.value.keypair read.value) :=
  focusPrefix_erases _ _ (Encryption.observe_erases _ _ _)

theorem packet_erases (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId) :
    ErasesPrefix (packet headId head id)
      (do encryptPacket Env.checksumHelp head.value.keypair (← liftWG (getTxSkb id))) := by
  unfold packet
  apply captureRun_bind_erases
  intro read
  exact crypt_erases headId head id read

theorem tail_erases (item : Option (List SkbId)) :
    ErasesPrefix (tail item) (RxWorkers.encryptStepTailSource item) := by
  cases item with
  | none =>
    unfold tail RxWorkers.encryptStepTailSource
    exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _)
  | some first =>
    cases selected : first.head?
    all_goals unfold tail afterHead RxWorkers.encryptStepTailSource packet
    all_goals simp only [selected,bind_assoc]
    all_goals repeat' first
      | (maintenance_head crypt; exact crypt_erases _ _ _ _)
      | (maintenance_head captureRun; apply captureRun_bind_erases)
      | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
      | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
      | (maintenance_head Bind.bind; first
          | apply captureRun_bind_erases
          | apply erasesPrefix_bind)
      | (maintenance_head ForIn.forIn; apply erasesPrefix_forIn)
      | maintenance_intro
      | dsimp (config := {failIfUnchanged := true}) only
      | split

theorem crypt_safe (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (read : RunWitness DataPacket) (hh : head.Valid (liftWG (getTxSkb headId)))
    (hr : read.Valid (liftWG (getTxSkb id))) :
    PrefixPreserves (fun h _ => Good h) Good (crypt headId head id read) := by
  intro w h hi
  obtain ⟨suffix,eq,_,valid⟩ := Encryption.observe_receipts Env.checksumHelp head.value.keypair read.value w
    (h.filterMap (fun r => some r.cipher))
  have out := focusPrefix_suffix (fun r => (⟨headId,head,id,read,r⟩ : Receipt))
    (fun r => some r.cipher) _ w h _ suffix (Prod.ext rfl eq)
  change runPrefix (crypt headId head id read) w h = _ at out
  rw [out]
  have good : Good (h ++ suffix.map (fun r => ⟨headId,head,id,read,r⟩)) := by
    intro r member
    rcases List.mem_append.mp member with old | fresh
    · exact hi r old
    · obtain ⟨cipher,inSuffix,rfl⟩ := List.mem_map.mp fresh
      exact ⟨hh,hr,valid cipher inSuffix⟩
  refine ⟨suffix.map (fun r => ⟨headId,head,id,read,r⟩),rfl,good,?_⟩
  cases (runPrefix (Encryption.observe Env.checksumHelp head.value.keypair read.value) w
    (h.filterMap (fun r => some r.cipher))).1 <;> trivial


private theorem capture_safe (a : Leanux.M α) :
    PrefixEnsures (fun h _ => Good h) Good (captureRun a)
      (fun r h _ => Good h ∧ r.Valid a) :=
  PrefixEnsures.captureRun a (fun _ _ hi => hi) (fun _ _ _ _ hi run => ⟨hi,run⟩)

private theorem lift_safe (a : Leanux.M α) :
    PrefixPreserves (fun h _ => Good h) Good (liftPrefix a) :=
  (PrefixEnsures.lift (P := fun h (_ : World) => Good h) (S := Good)
    (Q := fun _ h (_ : World) => Good h) a (fun _ _ hi => hi) (fun _ _ _ _ hi _ => hi)).preserves

theorem packet_safe (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (hh : head.Valid (liftWG (getTxSkb headId))) :
    PrefixPreserves (fun h _ => Good h) Good (packet headId head id) := by
  apply PrefixEnsures.preserves
  unfold packet
  apply PrefixEnsures.bind (capture_safe _)
  intro read w h hi
  exact crypt_safe headId head id read hh hi.2 w h hi.1

macro "worker_good_step" : tactic => `(tactic| first
  | (nonce_product_head liftPrefix; exact lift_safe _)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun h (_ : World) (hi : Good h) => hi) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ (fun h (_ : World) (hi : Good h) => hi))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem afterHead_safe (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket)
    (hh : head.Valid (liftWG (getTxSkb headId))) :
    PrefixPreserves (fun h _ => Good h) Good (afterHead first headId head) := by
  unfold afterHead
  repeat' first
    | (nonce_product_head packet; exact packet_safe _ _ _ hh)
    | worker_good_step

theorem tail_safe (item : Option (List SkbId)) :
    PrefixPreserves (fun h _ => Good h) Good (tail item) := by
  unfold tail
  apply PrefixPreserves.bind (lift_safe _)
  intro _
  cases item with
  | none => exact PrefixPreserves.pure (fun h (_ : World) (hi : Good h) => hi) _
  | some first =>
    dsimp only
    cases selected : first.head? with
    | none => exact lift_safe _
    | some headId =>
      simp only
      apply PrefixEnsures.preserves
      apply PrefixEnsures.bind (capture_safe _)
      intro head w h hi
      exact afterHead_safe first headId head hi.2 w h hi.1


/-- Every receipt in a fresh worker tail captures its actual head and packet
reads and native AEAD expression, even if later work stops. -/
theorem tail_receipts (item : Option (List SkbId)) (w : World) :
    Good (runPrefix (tail item) w []).2 := by
  obtain ⟨_,_,safe,_⟩ := tail_safe item w [] (by intro r impossible; simp at impossible)
  exact safe

end Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
