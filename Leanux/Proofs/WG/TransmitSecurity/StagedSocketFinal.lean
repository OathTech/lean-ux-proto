import Leanux.Proofs.WG.TransmitSecurity.StagedEncryptionFinal
import Leanux.Proofs.WG.TransmitSecurity.SocketCiphertextBinding
import Leanux.Proofs.WG.HandshakeSecurity.AllocationOwnerBinding

/-! Native socket receipts join historical staging authorization, actual AEAD
bytes, the packet's selected current key and the endpoint read at send. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects HandshakeSecurity

/-- A transport socket payload cannot be substituted across packet peers.
Its native receipt has the actual endpoint/bytes, an earlier AEAD under its
peer's selected current key, historical ownership at allocation, and an earlier
routed or keepalive plaintext origin. Later retirement may clear the owner word. -/
theorem initialized_socket (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (r : Completion.SocketReceipt)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .old (.socket r) :: post) :
    r.Valid ∧ r.packet.value.peer = r.pid ∧
      SocketEmission r.endpoint r.packet.value.bytes r.packet.value.ds
        r.socket.before.wg.sent r.socket.after.wg.sent ∧
      ∃ cipher : WorkerEncryption.Receipt,
        CausalJournal.Event.old (.encrypted cipher) ∈ pre ∧ cipher.Valid ∧
        cipher.read.value.peer = r.pid ∧
        r.packet.value.bytes = cipher.cipher.ciphertext ∧
        AllocationOwner.Historical (pre.filterMap CausalJournal.old?) cipher ∧
        AllocationSelection.Earlier (pre.filterMap CausalJournal.old?) r.pid r.packet.value.keypair
          (Responder.keyCore cipher.cipher.keyRead.value) ∧
        ∃ generation stamp ticket, Born pre generation r.pid stamp ticket r.packet.value.plaintext := by
  have bound := SocketCiphertext.final_initialized trace placeholders
  obtain ⟨valid,peer,emission,_,_,cipher,encryptedMember,cipherValid,_,_,material⟩ :=
    bound (pre.filterMap CausalJournal.old?) r (post.filterMap CausalJournal.old?) (by
      rw [position]
      simp only [List.filterMap_append,List.filterMap_cons,CausalJournal.old?])
  obtain ⟨event,eventMember,decoded⟩ := List.mem_filterMap.mp encryptedMember
  have encoded : event = Journal.Event.encrypted cipher := by
    cases event <;> simp only [Journal.encryption?,Option.some.injEq,reduceCtorEq] at decoded
    subst cipher
    rfl
  subst event
  have member := old_member eventMember
  obtain ⟨before,after,atCipher⟩ := List.mem_iff_append.mp member
  have cipherPosition : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      before ++ .old (.encrypted cipher) :: (after ++ .old (.socket r) :: post) := by
    rw [position,atCipher]
    simp only [List.append_assoc,List.cons_append]
  obtain ⟨_,generation,stamp,ticket,born⟩ := initialized_encryption trace placeholders before _ cipher cipherPosition
  obtain ⟨_,owned,selected⟩ := AllocationOwner.final_encryption trace placeholders
    (before.filterMap CausalJournal.old?) ((after ++ .old (.socket r) :: post).filterMap CausalJournal.old?)
    cipher (by rw [cipherPosition]; simp only [List.filterMap_append,List.filterMap_cons,CausalJournal.old?])
  have peerSame : cipher.read.value.peer = r.pid := by
    have same := congrArg DataPacket.peer material
    exact (show cipher.read.value.peer = r.packet.value.peer from same).trans peer
  have keySame : cipher.read.value.keypair = r.packet.value.keypair := by
    simpa only [PacketPayload.material] using congrArg DataPacket.keypair material
  have plainSame : cipher.read.value.plaintext = r.packet.value.plaintext := by
    simpa only [PacketPayload.material] using congrArg DataPacket.plaintext material
  have bytes : r.packet.value.bytes = cipher.cipher.ciphertext :=
    (congrArg DataPacket.bytes material).symm
  refine ⟨valid,peer,emission,cipher,member,cipherValid,peerSame,bytes,?_,?_,generation,stamp,ticket,?_⟩
  · rw [atCipher,List.filterMap_append]
    exact owned.append
  · rw [atCipher,List.filterMap_append]
    simpa only [peerSame,keySame] using selected.append (suffix :=
      (.old (.encrypted cipher) :: after).filterMap CausalJournal.old?)
  · rw [atCipher,←peerSame,←plainSame]
    exact born.append _

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
