import Leanux.Proofs.WG.RetirementSecurity.ReadySocketJournalFinal
import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginFinal
import Leanux.Proofs.WG.TransmitSecurity.SocketJournalFinal
import Leanux.Proofs.WG.TransmitSecurity.CompletionEmission

/-! Every actual socket payload has an earlier native AEAD certificate.
Initialized ready-batch facts discharge the empty-cell exception. -/
namespace Leanux.Proofs.WG.TransmitSecurity.SocketCiphertext
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open AuthenticatedEffects RetirementSecurity

def Bound (pre : List Journal.Event) (r : Completion.SocketReceipt) : Prop :=
  r.Valid ∧ r.packet.value.peer = r.pid ∧
    SocketEmission r.endpoint r.packet.value.bytes r.packet.value.ds
      r.socket.before.wg.sent r.socket.after.wg.sent ∧
    ∃ generation, PacketOrigins.epoch r.packet.before.wg = some generation ∧
      CiphertextOrigins.Certificate (CiphertextOrigins.receipts pre) generation r.id
        (PacketPayload.material r.packet.value)

def Safe (h : List Journal.Event) : Prop :=
  ∀ pre r post, h = pre ++ Journal.Event.socket r :: post → Bound pre r

theorem join (valid : Journal.SocketHistory.Safe h) (peer : SocketJournal.Safe h)
    (ready : ReadySocketJournal.Safe h) (origin : CiphertextOrigins.Safe h) : Safe h := by
  intro pre r post position
  have member : Journal.Event.socket r ∈ h := by rw [position]; simp
  have socket : r ∈ h.filterMap Journal.SocketHistory.socket? :=
    List.mem_filterMap.mpr ⟨_,member,rfl⟩
  have sound := valid r socket
  refine ⟨sound,peer r socket,sound.emission,?_⟩
  have nonempty : r.packet.value.bytes ≠ [] := ready r (List.mem_filterMap.mpr ⟨_,member,rfl⟩)
  obtain ⟨kept,resident⟩ := CiphertextOrigins.read_cell r.packet sound.1
  rw [kept] at resident
  cases device : r.packet.before.wg.dev with
  | none => simp [TxDisposition.txPackets,device] at resident
  | some d =>
    have epoch : PacketOrigins.epoch r.packet.before.wg = some d.ifindex := by
      simp [PacketOrigins.epoch,device]
    exact ⟨d.ifindex,epoch,origin pre (.socket r) post position d.ifindex epoch nonempty⟩

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  join (Journal.SocketHistory.initialized trace placeholders)
    (SocketJournal.Scheduler.initialized trace placeholders)
    (ReadySocketJournal.Scheduler.initialized trace placeholders)
    (CiphertextOrigins.initialized trace placeholders)

theorem final_initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.old?) := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [←history]
  exact initialized trace placeholders

end Leanux.Proofs.WG.TransmitSecurity.SocketCiphertext
