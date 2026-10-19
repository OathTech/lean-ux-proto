import Leanux.Proofs.WG.TransmitSecurity.BatchNativeStagingFrames

/-! The native nonce loop constructs homogeneous packet arguments. Its native
key checks and early refusal preserve older queued batches before allocation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem constant {P : WGWorld → Prop} {C : Prop} {action : WG.M α}
    (keeps : Preserves P action) : Preserves (fun w => P w ∧ C) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp keeps w a result v b before.1 run,before.2⟩

private theorem loop (xs : List α) (initial : β) (body : α → β → WG.M (ForInStep β))
    (I : β → WGWorld → Prop)
    (keeps : ∀ x acc, Hoare (body x acc) (I acc)
      (fun step => match step with | .done next => I next | .yield next => I next)) :
    Hoare (forIn xs initial body) (I initial) I := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  induction xs generalizing initial w a with
  | nil => cases run; exact before
  | cons x xs ih =>
    rw [List.forIn_cons,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨step,u,c,first,rest⟩ := run
    have kept := (hoare_iff_run_ambient _ _ _).mp (keeps x initial) w a step u c before first
    cases step with
    | done next => cases rest; exact kept
    | yield next => exact ih next u c kept rest

private theorem finish (value : α) : Hoare (pure value : WG.M α) (Ready locals) (fun _ => Inv) :=
  hoare_consequence (preserves_pure value) (fun _ h => h) (fun _ _ h => h.2)

private theorem weaken {action : WG.M α} (rule : Preserves (Ready locals) action) :
    Hoare action (Ready locals) (fun _ => Inv) :=
  hoare_consequence rule (fun _ h => h) (fun _ _ h => h.2)

theorem key_source (locals : List TxLocalBatch) (pid kid : Nat) (packets : List WG.Packet) :
    Hoare (stagedKeySource pid kid packets) (Ready locals) (fun _ => Inv) := by
  let P := Ready locals
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  have expired (date : Int64) : Preserves P (branchExpired .stagedBirthdateExpired date REJECT_AFTER_TIME) :=
    (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn (pkt : WG.Packet) : Preserves P (ipTunnelEcnEncap pkt) :=
    (ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out (invalid : Bool) := ready_no_key (locals := locals) pid packets (some kid) invalid
  unfold stagedKeySource
  apply hoare_bind _ _ (ready_read_key kid)
  intro k
  apply hoare_bind _ _ (ambient (AmbientM.branch _ _))
  intro invalid
  split
  · exact weaken (out false)
  · apply hoare_bind _ _ (expired k.sending.birthdate)
    intro expired
    split
    · exact weaken (out true)
    · apply hoare_consequence (P := fun w => P w ∧ BatchHistory.Aligned pid kid [])
      · apply hoare_bind _ _ (Q := fun acc : Option Unit × List DataPacket =>
            fun w => P w ∧ BatchHistory.Aligned pid kid acc.2)
        · apply loop _ _ _ (fun acc : Option Unit × List DataPacket =>
              fun w => P w ∧ BatchHistory.Aligned pid kid acc.2)
          intro pkt acc
          apply hoare_bind _ _ (constant (ambient (AmbientM.branch _ _)))
          intro _
          apply hoare_bind _ _ (constant (ecn pkt))
          intro ds
          apply hoare_bind _ _ (constant (ready_read_key kid))
          intro key
          apply hoare_bind _ _ (constant (ready_set_key kid _))
          intro _
          apply hoare_bind _ _ (constant (ambient (AmbientM.branchCmp _ _ _ _)))
          intro rejected
          cases rejected with
          | true =>
            apply hoare_bind _ _ (constant (out true))
            intro result
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro w a result v b before run
            cases run
            exact before
          | false =>
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro w a result v b before run
            cases run
            refine ⟨before.1,?_⟩
            intro packet member
            rcases List.mem_append.mp member with old | new
            · exact before.2 packet old
            · have same : packet = DataPacket.mk pid kid key.sendingCounter pkt ds .uncrypted [] := by
                simpa using new
              subst packet
              exact ⟨rfl,rfl⟩
        · intro acc
          obtain ⟨done,data⟩ := acc
          cases done with
          | some result =>
            exact hoare_consequence (finish result) (fun _ h => h.1) (fun _ _ h => h)
          | none =>
            apply hoare_bind _ _ (constant (ambient (AmbientM.branch _ _)))
            intro _
            apply (hoare_iff_run_ambient _ _ _).mpr
            intro w a result v b before run
            exact (hoare_iff_run_ambient _ _ _).mp (submit pid kid data before.2)
              w a result v b before.1 run
      · intro w before
        exact ⟨before,by intro packet member; cases member⟩
      · exact fun _ _ h => h

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
