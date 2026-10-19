import Leanux.Proofs.WG.TransmitSecurity.StagedAllocationFinal
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverOuter

/-! Each actual encrypted plaintext keeps its own earlier staging occurrence,
through the native allocation certificate in the same initialized journal. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

theorem Aligned.member (aligned : Aligned R xs ys) (member : y ∈ ys) : ∃ x, R x y := by
  induction aligned with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | inside
    · subst y; exact ⟨_,head⟩
    · exact ih inside

theorem Batch.member (batch : Batch history generation pid stamp packets)
    (member : packet ∈ packets) : ∃ ticket, Born history generation pid stamp ticket packet := by
  obtain ⟨_,_,aligned⟩ := batch
  exact aligned.member member

/-- Encryption cannot invent plaintext or transfer it to another packet peer.
Every initialized AEAD has an actual earlier routed or keepalive staging
occurrence for its own plaintext and peer, including before later Stop. -/
theorem initialized_encryption (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .old (.encrypted r) :: post) :
    r.Valid ∧ ∃ generation stamp ticket,
      Born pre generation r.read.value.peer stamp ticket r.read.value.plaintext := by
  have projected := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at projected
  have origins := PacketOrigins.initialized trace placeholders
  rw [projected] at origins
  obtain ⟨valid,_,_,packets,allocation,member,_,_,index,input,atInput,_,material⟩ :=
    origins (pre.filterMap CausalJournal.old?) (.encrypted r) (post.filterMap CausalJournal.old?) (by
      rw [position]
      simp only [List.filterMap_append,List.filterMap_cons,CausalJournal.old?])
  have member := old_member member
  obtain ⟨before,after,atAllocation⟩ := List.mem_iff_append.mp member
  have allocationPosition : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      before ++ .old (.allocated packets allocation) :: (after ++ .old (.encrypted r) :: post) := by
    rw [position,atAllocation]
    simp only [List.append_assoc,List.cons_append]
  obtain ⟨_,pid,peer,slot,_,generation,_,_,_,_,batch,shape⟩ :=
    initialized_allocation trace placeholders before _ packets allocation allocationPosition
  have inside := List.mem_of_getElem? atInput
  have peerSame : r.read.value.peer = pid := by
    have same := congrArg DataPacket.peer material
    simpa only [PacketMaterial.material] using same.symm.trans (shape.2 input inside).1
  have plaintextSame : input.plaintext = r.read.value.plaintext := by
    simpa only [PacketMaterial.material] using congrArg DataPacket.plaintext material
  obtain ⟨ticket,born⟩ := batch.member (List.mem_map.mpr ⟨input,inside,rfl⟩)
  refine ⟨valid,generation,peer.internalId,ticket,?_⟩
  rw [peerSame,←plaintextSame,atAllocation]
  exact born.append _

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
