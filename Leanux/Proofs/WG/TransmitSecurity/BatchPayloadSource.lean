import Leanux.Proofs.WG.TransmitSecurity.BatchPayloadFrames

/-! Actual selection, reservation and allocation receipts. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchPayload
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem selection (pid : PeerId) :
    StatePrefixEnsures (fun h _ _ => Safe h) Safe (Journal.selection pid)
      (fun value h _ _ => Safe h ∧ ∀ peer kid, value = some (peer,some kid) → Selected h pid peer kid) := by
  intro w a h hi
  unfold Journal.selection HandshakeSecurity.Responder.DriverCuts.selection
  rw [HandshakeSecurity.ExchangeCausalSession.focus_receipt]
  have equation := runWGPrefix_receiptWGObserved
    (liftWGPrefix (HandshakeSecurity.Responder.selectionPrefix pid))
    (Journal.Event.responder ∘ HandshakeSecurity.Responder.DriverCuts.Event.selected pid) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((HandshakeSecurity.Responder.selectionPrefix pid).run w).run a with
  | error stop => exact ⟨[],by simp,hi,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let r : WGRunWitness (Option (Peer × Option KeypairId)) := ⟨value,w,v,a,b⟩
    have safe := hi.quiet (event := .responder (.selected pid r)) rfl
    refine ⟨[.responder (.selected pid r)],rfl,safe,safe,?_⟩
    intro peer kid returned
    exact ⟨r,by simp [r],run,returned⟩

theorem reserve (slot : KeypairId) (mono : Monotone P) :
    StatePrefixPreserves (Keep P) Safe (Journal.reserve slot) :=
  quiet ((StateAppends.focus _ _ _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved
      (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved slot).run w)) _ (fun _ => rfl)) mono

theorem allocate (packets : List DataPacket) :
    StatePrefixEnsures (Keep (fun h => Source h packets)) Safe (Journal.allocate packets)
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

end Leanux.Proofs.WG.TransmitSecurity.BatchPayload
