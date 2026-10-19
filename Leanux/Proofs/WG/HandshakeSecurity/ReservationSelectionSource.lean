import Leanux.Proofs.WG.HandshakeSecurity.ReservationSelectionFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSessionSource

/-! The actual selected receipt establishes the current-key cut; each native
reservation preserves that core and records its preceding selection. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReservationSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Responder

theorem selection (pid : PeerId) :
    StatePrefixEnsures (fun h _ _ => Safe h) Safe (Journal.selection pid)
      (fun value h w _ => Safe h ∧ ∀ peer kid, value = some (peer,some kid) → Picked h kid w) := by
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
    exact ⟨h,[],pid,r,peer,rfl,returned,resident⟩

theorem reserve (slot : KeypairId) :
    StatePrefixPreserves (Keep (fun h w => Picked h slot w)) Safe (Journal.reserve slot) := by
  have inner : StatePrefixPreserves (Keep (fun h w => Picked h slot w)) Safe
      (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot)) :=
    quiet (StateAppends.focus _ _ _)
      (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved slot).run w))
      (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases slot))
      (ResidentMaterial.core_of_same (StagingMaterial.reserve_pool slot))
  have capture : StatePrefixEnsures (Keep (fun h w => Picked h slot w)) Safe
      (captureWGObserved (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot)))
      (fun r h w _ => Safe h ∧ Picked h slot w ∧ Picked h slot r.before ∧ r.Valid (Nonce.reserveNative slot)) := by
    apply (StatePrefixEnsures.captureWGObserved inner).consequence (fun _ _ _ hi => hi)
    intro r h w a post
    obtain ⟨after,_,kept,h0,before,run⟩ := post
    have erased := focusStatePrefix_erases Journal.Event.nonce Journal.nonce?
      (Nonce.reserveObserved_erases slot) r.before r.ambientBefore h0
    change (runWGPrefix (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot))
      r.before r.ambientBefore h0).1 = _ at erased
    rw [run] at erased
    obtain ⟨token,valid,recorded⟩ := ReservationReceipts.observed slot r erased.symm h0
    rw [run] at recorded
    have history := congrArg Prod.snd recorded
    dsimp only at history
    refine ⟨kept.1,after ▸ kept.2,?_,valid.1⟩
    rw [history]
    exact before.2.transport (Responder.Retains.refl _)
  unfold Journal.reserve receiptWGObserved
  apply StatePrefixEnsures.bind capture
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ => Keep (fun h w => Picked h slot w))
  · apply StatePrefixEnsures.emit (Journal.Event.reserved slot r)
    · intro h w a hi
      apply hi.1.append
      intro pre event post position
      cases pre with
      | nil =>
        simp only [List.nil_append,List.cons.injEq] at position
        obtain ⟨same,_⟩ := position
        subst event
        exact ⟨hi.2.2.2,by simpa only [List.append_nil] using hi.2.2.1⟩
      | cons e es =>
        have sizes := congrArg List.length position
        simp only [List.length_append,List.length_cons,List.length_nil] at sizes
        omega
    · intro h w a hi
      constructor
      · apply hi.1.append
        intro pre event post position
        cases pre with
        | nil =>
          simp only [List.nil_append,List.cons.injEq] at position
          obtain ⟨same,_⟩ := position
          subst event
          exact ⟨hi.2.2.2,by simpa only [List.append_nil] using hi.2.2.1⟩
        | cons e es =>
          have sizes := congrArg List.length position
          simp only [List.length_append,List.length_cons,List.length_nil] at sizes
          omega
      · exact hi.2.1.transport (Responder.Retains.refl _)
  · intro _
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

end Leanux.Proofs.WG.HandshakeSecurity.ReservationSelection
