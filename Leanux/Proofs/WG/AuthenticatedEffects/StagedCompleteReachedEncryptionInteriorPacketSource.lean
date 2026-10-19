import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorTrace

/-! Fixed original packet-read, encryption and byte-write boundaries. The
captured read belongs to the same current native world as the encryption,
and the ciphertext result supplies the exact subsequent byte setter. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open EncryptionPacket

def crypt (headId : SkbId) (head : RunWitness DataPacket) (skb : SkbId) (read : RunWitness DataPacket) :
    PrefixM CausalJournal.Event (Option (List UInt8)) :=
  focusPrefix (CausalJournal.Event.old ∘ Journal.Event.encrypted)
    (fun event => (CausalJournal.old? event).bind Journal.encryption?) (WorkerEncryption.crypt headId head skb read)

theorem packet_factor (headId : SkbId) (head : RunWitness DataPacket) (skb : SkbId) :
    ops.packet headId head skb = (do
      let read ← captureRun (liftWG (getTxSkb skb))
      crypt headId head skb read) := by
  have capture : Appends (captureRun (Event := WorkerEncryption.Receipt) (liftWG (getTxSkb skb))) := by
    intro w history
    refine ⟨[],?_⟩
    rw [runPrefix_captureRun]
    cases (liftWG (getTxSkb skb)).run w <;> simp
  have distributed : ops.packet headId head skb = (do
      let read ← ops.head skb
      crypt headId head skb read) := by
    funext w history
    exact (focusPrefix_bind_appends (CausalJournal.Event.old ∘ Journal.Event.encrypted)
      (fun event => (CausalJournal.old? event).bind Journal.encryption?) (fun _ => rfl)
      capture (fun _ => Appends.focus _ _ _) w history).symm
  rw [distributed,head_eq]

def readPrefix (skb : SkbId) : PrefixM CausalJournal.Event (RunWitness DataPacket) := do
  _ ← ops.step (branch .encWorkerSkbIterate true)
  captureRun (liftWG (getTxSkb skb))

def afterCrypt (skb : SkbId) (state : PacketState) (encrypted : Option (List UInt8)) :
    PrefixM CausalJournal.Event (ForInStep PacketState) := do
  if ← ops.step (branch .encWorkerEncrypted encrypted.isSome) then
    ops.step (liftWG (setTxSkb skb fun packet => {packet with bytes := encrypted.getD []}))
    pure (.yield state)
  else pure (.done .dead)

theorem iteration_factor (headId : SkbId) (head : RunWitness DataPacket) (skb : SkbId) (state : PacketState) :
    iteration headId head skb state = (do
      let read ← readPrefix skb
      let encrypted ← crypt headId head skb read
      afterCrypt skb state encrypted) := by
  simp only [iteration,packet_factor,readPrefix,afterCrypt,bind_assoc]

def writePrefix (headId : SkbId) (head : RunWitness DataPacket) (skb : SkbId) :
    PrefixM CausalJournal.Event (RunWitness DataPacket × Option (List UInt8)) := do
  let read ← readPrefix skb
  let encrypted ← crypt headId head skb read
  _ ← ops.step (branch .encWorkerEncrypted encrypted.isSome)
  pure (read,encrypted)

def writeTail (skb : SkbId) (state : PacketState) (encrypted : Option (List UInt8)) :
    PrefixM CausalJournal.Event (ForInStep PacketState) := do
  if encrypted.isSome then
    ops.step (liftWG (setTxSkb skb fun packet => {packet with bytes := encrypted.getD []}))
    pure (.yield state)
  else pure (.done .dead)

/-- The observed branch is native bookkeeping and returns its actual input;
the byte setter remains after it, on exactly the successful branch. -/
theorem write_factor (headId : SkbId) (head : RunWitness DataPacket) (skb : SkbId) (state : PacketState) :
    iteration headId head skb state =
      (writePrefix headId head skb >>= fun (_,encrypted) => writeTail skb state encrypted) := by
  rw [iteration_factor]
  simp only [writePrefix,bind_assoc,pure_bind]
  apply congrArg (fun next => readPrefix skb >>= next)
  funext read
  apply congrArg (fun next => crypt headId head skb read >>= next)
  funext encrypted
  funext w history
  change runPrefix (afterCrypt skb state encrypted) w history =
    runPrefix (ops.step (branch .encWorkerEncrypted encrypted.isSome) >>= fun _ => writeTail skb state encrypted) w history
  simp only [afterCrypt,writeTail,runPrefix_bind,branch_run]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
