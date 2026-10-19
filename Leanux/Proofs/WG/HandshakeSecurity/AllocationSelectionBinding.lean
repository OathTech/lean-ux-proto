import Leanux.Proofs.WG.HandshakeSecurity.AllocationSelectionInitialized
import Leanux.Proofs.WG.HandshakeSecurity.InitializedEncryptionMaterial
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! Each actual AEAD uses the immutable key core selected as current by that
same packet's peer. The initialized packet allocation certificate supplies the
identity link; slot equality alone is not used to identify the peer. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.AllocationSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Responder Lifetimes

theorem Safe.prefix (safe : Safe (h ++ suffix)) : Safe h := by
  intro pre event post position
  apply safe pre event (post ++ suffix)
  rw [position]
  simp only [List.append_assoc,List.cons_append]

theorem selected_of_binding (safe : Safe h) (bound : ResidentMaterial.BoundReceipt h r) :
    Earlier h r.read.value.peer r.read.value.keypair (keyCore r.cipher.keyRead.value) := by
  obtain ⟨generation,_,packets,allocation,n,input,member,_,_,atInput,_,material,resident⟩ := bound
  obtain ⟨before,after,position⟩ := List.mem_iff_append.mp member
  have selected := (safe before (.allocated packets allocation) after position).2 input
    (List.mem_of_getElem? atInput) _ resident
  have peer : input.peer = r.read.value.peer := by
    simpa only [PacketMaterial.material] using congrArg DataPacket.peer material
  have key : input.keypair = r.read.value.keypair := by
    simpa only [PacketMaterial.material] using congrArg DataPacket.keypair material
  have full := selected.append (suffix := .allocated packets allocation :: after)
  simpa only [←position,peer,key] using full

/-- The actual initialized AEAD key core belongs to the same packet peer's
strictly earlier native current-slot selection. No incoming invariant or H1
frame is needed for this source/dataflow statement. -/
theorem initialized_encryption (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 = pre ++ .encrypted r :: post) :
    r.Valid ∧ Earlier pre r.read.value.peer r.read.value.keypair (keyCore r.cipher.keyRead.value) := by
  obtain ⟨valid,bound⟩ := ResidentMaterial.initialized trace placeholders pre (.encrypted r) post position
  have member : r ∈ ((runPrefixOuter (Journal.execute trace placeholders) []).2).filterMap Journal.encryption? := by
    rw [position]
    exact List.mem_filterMap.mpr ⟨.encrypted r,by simp,rfl⟩
  have batch := (BatchJournal.Scheduler.initialized trace placeholders r member).2.2
  have selections := initialized trace placeholders
  rw [position] at selections
  exact ⟨valid,selected_of_binding selections.prefix (bound batch)⟩

/-- The original current key read and the actual allocation, role and sending
material are exposed at the staging selection time. -/
theorem Earlier.current (before : Earlier h pid slot core) :
    ∃ pre post r peer d,
      h = pre ++ Journal.Event.responder (.selected pid r) :: post ∧
      r.Valid (selectionPrefix pid) ∧ r.value = some (peer,some slot) ∧
      r.before.dev = some d ∧ d.peers[pid]? = some peer ∧ peer.keypairCurrent = some slot ∧
      current r.before pid = some core := by
  obtain ⟨pre,post,r,peer,position,valid,selected,material⟩ := before
  obtain ⟨d,device,stored,slotWord⟩ := DriverCuts.selection_native pid r valid peer slot selected
  have same := (hoare_iff_run_ambient _ _ _).mp (DriverCuts.selection_core pid (pool r.before))
    _ _ _ _ _ rfl valid
  exact ⟨pre,post,r,peer,d,position,valid,selected,device,stored,slotWord,
    DriverCuts.selection_current pid r valid peer slot selected core (same ▸ material)⟩

theorem final_encryption (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
      AuthenticatedEffects.CausalJournal.old?) = pre ++ .encrypted r :: post) :
    r.Valid ∧ Earlier pre r.read.value.peer r.read.value.keypair (keyCore r.cipher.keyRead.value) := by
  have history := congrArg Prod.snd (AuthenticatedEffects.CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  exact initialized_encryption trace placeholders pre post r (history.trans position)

end Leanux.Proofs.WG.HandshakeSecurity.AllocationSelection
