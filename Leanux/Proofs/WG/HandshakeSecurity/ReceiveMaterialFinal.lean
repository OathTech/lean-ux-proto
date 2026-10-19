import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialInitialized
import Leanux.Proofs.WG.HandshakeSecurity.ResponderEncryptionInitialized

/-! Initialized confirmation attribution and actual responder encryption use
one journal and one allocation identity. The exact final observer projection
retains the chronology; the source carrier supplies the decrypting incarnation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues AuthenticatedEffects TransmitSecurity Responder

/-- Initialized native confirmation refers to its own immediately preceding
accepted counter receipt and the exact earlier authenticating allocation. -/
theorem initialized_confirmation (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (event : Journal.Event) (pid : PeerId) (kid : KeypairId)
    (r : WGRunWitness Bool)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 = pre ++ event :: post)
    (recorded : Journal.responder? event = some (.confirmed pid kid r)) :
    r.Valid (receivedWithKeypair pid kid) ∧
    ∀ core, pool r.before kid = some core →
      ∃ earlier counter, pre = earlier ++ [Journal.Event.replay counter] ∧
        counter.packet.peer = pid ∧ counter.packet.keypair = kid ∧ counter.run.value = true ∧
        Replay.Certified (earlier.filterMap Journal.origin?) counter ∧
        Certificate (earlier.filterMap Journal.origin?) counter.skb counter.packet r.before core :=
  (Execution.initialized trace placeholders).2 pre event post position pid kid r recorded

theorem final_history (trace : Runner.Trace) (placeholders : Bool) :
    Execution.Safe ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.old?) := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  rw [←history]
  exact Execution.initialized trace placeholders

/-- The final causal observer preserves initialized allocation attribution at
all native confirmation events, including internally stopped receive suffixes. -/
theorem final_confirmation (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (event : Journal.Event)
    (position : ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap
      CausalJournal.old?) = pre ++ event :: post) : Confirmation.Checked pre event :=
  (final_history trace placeholders).2 pre event post position

/-- Strictly earlier successful confirmation and the authenticated receive
share the actual key allocation named by a later encryption. The certificate's
native_aead eliminator exposes the decrypting resident key and its internalId. -/
def PriorAllocationConfirmation (history : List Journal.Event) (allocation : Nat) : Prop :=
  ∃ left right event pid kid, ∃ r : WGRunWitness Bool, ∃ core : KeyCore,
    history = left ++ event :: right ∧
    Journal.responder? event = some (.confirmed pid kid r) ∧
    r.Valid (receivedWithKeypair pid kid) ∧ r.value = true ∧
    pool r.before kid = some core ∧ core.allocation = allocation ∧
    ∃ earlier counter, left = earlier ++ [Journal.Event.replay counter] ∧
      counter.packet.peer = pid ∧ counter.packet.keypair = kid ∧ counter.run.value = true ∧
      Replay.Certified (earlier.filterMap Journal.origin?) counter ∧
      Certificate (earlier.filterMap Journal.origin?) counter.skb counter.packet r.before core

/-- An initialized responder encryption has a strictly earlier successful
confirmation caused by a packet authenticated under that exact allocation.
Only the named local C2 H1 slot-rotation package remains an assumption. -/
theorem initialized_encryption (H1 : H1ResponderCurrentEdges)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 = pre ++ .encrypted r :: post)
    (responder : r.cipher.keyRead.value.iAmTheInitiator = false) :
    r.Valid ∧ PriorAllocationConfirmation pre r.cipher.keyRead.value.internalId := by
  obtain ⟨valid,left,right,event,pid,kid,confirmation,core,split,recorded,confirmed,accepted,resident,same,_⟩ :=
    Responder.initialized_encryption_confirmation H1 trace placeholders pre post r position responder
  have occurrence : (runPrefixOuter (Journal.execute trace placeholders) []).2 =
      left ++ event :: (right ++ .encrypted r :: post) := by
    rw [position,split]
    simp only [List.append_assoc,List.cons_append]
  have material : pool confirmation.before kid = some core := by
    cases device : confirmation.before.dev with
    | none => simp [keyCoreAt,device] at resident
    | some d => simpa [keyCoreAt,pool,device] using resident
  have certificate := (initialized_confirmation trace placeholders left _ event pid kid confirmation
    occurrence recorded).2 core material
  exact ⟨valid,left,right,event,pid,kid,confirmation,core,split,recorded,confirmed,accepted,material,same,certificate⟩

/-- Actual responder AEAD in the final observer requires strictly earlier
same-allocation authentication and successful confirmation. No reachability,
key funding, packet lifetime or independent-history premise is added. -/
theorem final_encryption (H1 : H1ResponderCurrentEdges)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : ((runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap
      CausalJournal.old?) = pre ++ .encrypted r :: post)
    (responder : r.cipher.keyRead.value.iAmTheInitiator = false) :
    r.Valid ∧ PriorAllocationConfirmation pre r.cipher.keyRead.value.internalId := by
  have history := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  exact initialized_encryption H1 trace placeholders pre post r (history.trans position) responder

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
