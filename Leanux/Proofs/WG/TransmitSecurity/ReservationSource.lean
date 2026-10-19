import Leanux.Proofs.WG.TransmitSecurity.ReservationHistory

/-! The actual shared reservation and allocation hooks carry completed native
receipts through the same journal, with source-local packet certificates. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
set_option maxHeartbeats 400000
set_option pp.structureInstances false

theorem reserve (slot : KeypairId) (mono : Monotone P) :
    StatePrefixEnsures (Keep P) Safe (Journal.reserve slot)
      (fun nonce h _ _ => Safe h ∧ P h ∧ Reserved h slot nonce) := by
  have inner : StatePrefixPreserves (Keep P) Safe
      (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot)) :=
    quiet (StateAppends.focus _ _ _)
      (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved slot).run w)) mono
  have capture : StatePrefixEnsures (Keep P) Safe
      (captureWGObserved (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot)))
      (fun r h _ _ => Safe h ∧ P h ∧ r.Valid (Nonce.reserveNative slot) ∧
        ∃ token, ReservationReceipts.Token slot r token ∧ Journal.Event.nonce token ∈ h) := by
    apply (StatePrefixEnsures.captureWGObserved inner).consequence (fun _ _ _ hi => hi)
    intro r h w a post
    obtain ⟨_,_,kept,h0,_,run⟩ := post
    refine ⟨kept.1,kept.2,?_⟩
    have erased := focusStatePrefix_erases Journal.Event.nonce Journal.nonce?
      (Nonce.reserveObserved_erases slot) r.before r.ambientBefore h0
    change (runWGPrefix (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot))
      r.before r.ambientBefore h0).1 = _ at erased
    rw [run] at erased
    have valid := erased.symm
    obtain ⟨token,same,recorded⟩ := ReservationReceipts.observed slot r valid h0
    rw [run] at recorded
    have histories : h = h0 ++ [.nonce token] := congrArg Prod.snd recorded
    exact ⟨valid,token,same,by rw [histories]; simp⟩
  unfold Journal.reserve receiptWGObserved
  apply StatePrefixEnsures.bind capture
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ h _ _ => Safe h ∧ P h ∧ Reserved h slot r.value)
  · apply StatePrefixEnsures.emit (Journal.Event.reserved slot r)
    · intro h w a hi
      exact hi.1.quiet rfl
    · intro h w a hi
      refine ⟨hi.1.quiet rfl,mono h _ (fun _ member => List.mem_append_left _ member) hi.2.1,
        r,by simp,hi.2.2.1,rfl,?_⟩
      obtain ⟨token,same,member⟩ := hi.2.2.2
      exact ⟨token,same,List.mem_append_left _ member⟩
  · intro _
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

theorem allocate (packets : List DataPacket) :
    StatePrefixEnsures (Keep (fun h => Packets h packets)) Safe (Journal.allocate packets)
      (fun _ h _ _ => Safe h) := by
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
        exact ⟨run,by simpa only [List.append_nil] using hi.2⟩
      | cons e es =>
        have sizes := congrArg List.length position
        simp only [List.length_append,List.length_cons,List.length_nil] at sizes
        omega
    exact ⟨[.allocated packets r],rfl,safe,safe⟩

end Leanux.Proofs.WG.TransmitSecurity.ReservationHistory
