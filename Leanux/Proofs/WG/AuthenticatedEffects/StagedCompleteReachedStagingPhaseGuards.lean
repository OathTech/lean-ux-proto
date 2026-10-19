import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseFrames

/-! The original finite nonce traversal preserves the full selected ledger
at every canonical point. Each successful original bind selects its real
successor; failed continuations retain the earlier point certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging Staging.Points
set_option maxHeartbeats 600000

theorem walk_covers (kid : KeypairId) (remaining : List Packet) (built : List DataPacket)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position)
      (walkShape pid kid remaining built) w a h := by
  induction remaining generalizing built h w a with
  | nil=>
    change Covers _ (.bind _ _) w a h
    have first:=selected_ambient (.branch .stagedNonceIterate false) _ rfl before
    exact covers_bind first (fun _ _ _ _ run=>first.normal run)
  | cons packet rest ih=>
    change Covers _ (.bind _ _) w a h
    have first:=selected_ambient (.branch .stagedNonceIterate true) _ rfl before
    apply covers_bind first
    intro iterate u b middle iterated
    have ecn:=selected_world (.ecn packet) (native_ecn packet) (first.normal iterated)
    apply covers_bind ecn
    intro ds v c last encoded
    have nonce:=selected_reserve kid (ecn.normal encoded)
    apply covers_bind nonce
    intro number q d events reserved
    have guard:=selected_ambient (.compare .stagedNonceRejected (number≥REJECT_AFTER_MESSAGES) number REJECT_AFTER_MESSAGES)
      _ rfl (nonce.normal reserved)
    apply covers_bind guard
    intro over r e tested test
    cases over <;> dsimp only
    · exact ih _ (guard.normal test)
    · exact guard.normal test

theorem guards_covers (key : Option KeypairId)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position)
      (guardsShape pid peer key) w a h := by
  unfold guardsShape
  change Covers _ (.bind _ _) w a h
  have first:=selected_ambient (.branch .stagedNoKeypair key.isNone) _ rfl before
  apply covers_bind first
  intro missing u b middle absent
  cases missing <;> dsimp only
  · cases key with
    | none=>exact first.normal absent
    | some kid=>
      have read:=selected_key kid (first.normal absent)
      apply covers_bind read
      intro key v c last found
      have guard:=selected_ambient (.branch .stagedKeyInvalid (!key.sending.isValid)) _ rfl (read.normal found)
      apply covers_bind guard
      intro invalid q d events tested
      cases invalid <;> dsimp only
      · have age:=selected_world (.age key.sending.birthdate) (Leanux.Proofs.Framing.branchExpired_sameWGWorld _ _ _ _) (guard.normal tested)
        apply covers_bind age
        intro expired r e final clocked
        cases expired <;> dsimp only
        · exact walk_covers kid peer.staged [] (age.normal clocked)
        · exact age.normal clocked
      · exact guard.normal tested
  · exact first.normal absent

theorem guard_point
    (before : CompleteCarrier.Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (point : Point (guardsShape pid peer key) u b middle leaf v c last remaining) :
    ∃ after generation,Staged.Obligations.Step ledger after ∧
      CompleteSelected.Ready after debts locals generation pid peer h.length last v c ∧
      runWGPrefix (checkedPrefix pid peer key) u b middle=runWGPrefix remaining v c last := by
  obtain ⟨after,generation,path,ready⟩:=selected_entry before selected
  obtain ⟨r,_,_,_,_,_,assigned,_⟩:=path
  have steps : Staged.Obligations.Step ledger after := assigned.symm ▸ transferLocation_step _ _ _
  exact ⟨after,generation,steps,(guards_covers key ready).point point,point.residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
