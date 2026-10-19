import Leanux.Proofs.WG.HandshakeSecurity.AllocationSelectionFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSessionSource

/-! The actual selection records its staging peer and current-key cut. Native
reservations retain that core; allocation records the same peer for each packet. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.AllocationSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Responder

theorem selection (pid : PeerId) :
    StatePrefixEnsures (fun h _ _ => Safe h) Safe (Journal.selection pid)
      (fun value h w _ => Safe h ∧ ∀ peer kid, value = some (peer,some kid) → Picked h pid kid w) := by
  intro w a h hi
  unfold Journal.selection DriverCuts.selection
  rw [ExchangeCausalSession.focus_receipt]
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (selectionPrefix pid))
    (Journal.Event.responder ∘ DriverCuts.Event.selected pid) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((selectionPrefix pid).run w).run a with
  | error stop => exact ⟨[],by simp,hi,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let r : WGRunWitness (Option (Peer × Option KeypairId)) := ⟨value,w,v,a,b⟩
    have safe := hi.quiet (event := .responder (.selected pid r)) rfl
    refine ⟨[.responder (.selected pid r)],rfl,safe,safe,?_⟩
    intro peer kid returned core resident
    exact ⟨h,[],r,peer,rfl,run,returned,resident⟩

def Aligned (pid : PeerId) (slot : KeypairId) (packets : List DataPacket) : Prop :=
  ∀ packet ∈ packets, packet.peer = pid ∧ packet.keypair = slot

theorem Aligned.append (before : Aligned pid slot packets) (packet : DataPacket)
    (peer : packet.peer = pid) (key : packet.keypair = slot) : Aligned pid slot (packets ++ [packet]) := by
  intro p member
  rcases List.mem_append.mp member with old | new
  · exact before p old
  · obtain rfl := List.mem_singleton.mp new
    exact ⟨peer,key⟩

theorem reserve (slot : KeypairId) :
    StatePrefixPreserves (Keep (fun h w => Picked h pid slot w ∧ C)) Safe (Journal.reserve slot) := by
  apply quiet
  · exact (StateAppends.focus _ _ _).receiptWGObserved _
  · exact StateHistoryFrame.receiptWGObserved
      (fun w => focusPrefix_other _ _ ReservationHistory.allocation? (fun _ => rfl) ((Nonce.reserveObserved slot).run w))
      _ (fun _ => rfl)
  · exact receiptWGObserved_erases (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases slot)) _
  · exact ResidentMaterial.core_of_same (StagingMaterial.reserve_pool slot)

theorem allocate (pid : PeerId) (slot : KeypairId) (packets : List DataPacket) :
    StatePrefixEnsures (Keep (fun h w => Picked h pid slot w ∧ Aligned pid slot packets)) Safe
      (Journal.allocate packets) (fun _ h _ _ => Safe h) := by
  intro w a h hi
  unfold Journal.allocate
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb))
    (Journal.Event.allocated packets) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((packets.mapM newTxSkb).run w).run a with
  | error stop => exact ⟨[],by simp,hi.1,True.intro⟩
  | ok out =>
    obtain ⟨⟨items,v⟩,b⟩ := out
    let r : WGRunWitness (List SkbId) := ⟨items,w,v,a,b⟩
    have safe : Safe (h ++ [.allocated packets r]) := by
      apply hi.1.append
      intro pre event post position
      cases pre with
      | nil =>
        simp only [List.nil_append,List.cons.injEq] at position
        obtain ⟨same,_⟩ := position
        subst event
        refine ⟨run,?_⟩
        intro packet member
        obtain ⟨peer,key⟩ := hi.2.2 packet member
        simpa only [List.append_nil,peer,key,r] using hi.2.1
      | cons e es =>
        have sizes := congrArg List.length position
        simp only [List.length_append,List.length_cons,List.length_nil] at sizes
        omega
    exact ⟨[.allocated packets r],rfl,safe,safe⟩

end Leanux.Proofs.WG.HandshakeSecurity.AllocationSelection
