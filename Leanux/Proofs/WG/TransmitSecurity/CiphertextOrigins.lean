import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrames
import Leanux.Proofs.WG.TransmitSecurity.WorkerCiphertextReceipts

/-! Resident wire bytes carry a certificate naming their actual encryption
receipt and packet allocation identity. Empty freshly allocated cells need no
certificate; a separate ready-batch contract will exclude that case at send. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition
variable {id : SkbId}

def Certificate (history : List WorkerEncryption.Receipt) (generation id : Nat)
    (value : DataPacket) : Prop :=
  ∃ r ∈ history, r.Valid ∧ r.id = id ∧
    PacketOrigins.epoch r.read.before.wg = some generation ∧
    PacketPayload.material {r.read.value with bytes := r.cipher.ciphertext} = value

def Inv (history : List WorkerEncryption.Receipt) (w : WGWorld) : Prop :=
  ∀ generation, PacketOrigins.epoch w = some generation → ∀ id packet,
    txPackets w id = some packet → packet.bytes ≠ [] →
      Certificate history generation id (PacketPayload.material packet)

theorem Certificate.mono (h : Certificate history generation id value)
    (included : history ⊆ later) : Certificate later generation id value := by
  obtain ⟨r,member,rest⟩ := h
  exact ⟨r,included member,rest⟩

theorem Inv.mono (h : Inv history w) (included : history ⊆ later) : Inv later w :=
  fun generation atEpoch id packet resident nonempty =>
    (h generation atEpoch id packet resident nonempty).mono included

theorem initial (net bare : Bool) : Inv [] (Runner.initialWG net bare) := by
  intro generation atEpoch id packet resident nonempty
  cases net <;> cases bare <;> simp [txPackets,Runner.initialWG] at resident

/-- Native allocation preserves certificates when its newly allocated cells
have the empty wire buffer supplied by staged-send construction. -/
theorem allocated (packets : List DataPacket) (empty : ∀ p ∈ packets, p.bytes = [])
    (r : WGRunWitness (List SkbId)) (valid : r.Valid (packets.mapM newTxSkb))
    (before : Inv h r.before) : Inv h r.after := by
  rcases r with ⟨item,w,v,a,b⟩
  change ((packets.mapM newTxSkb).run w).run a = .ok ((item,v),b) at valid
  intro generation atEpoch id packet resident nonempty
  cases device : w.dev with
  | none =>
    cases packets with
    | nil => cases valid; simp [txPackets,device] at resident
    | cons p ps =>
      simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at valid
      obtain ⟨_,_,_,first,_⟩ := valid
      simp [newTxSkb,liftSkb_run,device] at first
  | some d =>
    obtain ⟨_,_,e,afterDevice,_,epochEq,_⟩ := ItemSeparation.allocate_result packets device valid
    have beforeEpoch : PacketOrigins.epoch w = some generation := by
      simpa [PacketOrigins.epoch,device,afterDevice,epochEq] using atEpoch
    rcases PacketOrigins.allocation_origin packets device valid id packet resident with old | fresh
    · exact before generation beforeEpoch id packet old nonempty
    · obtain ⟨n,atPacket,_⟩ := fresh
      exact (nonempty (empty packet (List.mem_of_getElem? atPacket))).elim

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
