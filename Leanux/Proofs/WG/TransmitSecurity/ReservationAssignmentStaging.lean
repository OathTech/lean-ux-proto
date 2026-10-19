import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral
import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignmentSource

/-! The native staging loop assigns each accepted packet its own reservation
position. Allocation closes the interval so later batches cannot reuse it. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem forget {g : WGPrefix Journal.Event α} (rule : StatePrefixPreserves (Keep P) Safe g) :
    StatePrefixEnsures (Keep P) Safe g (fun _ h _ _ => Safe h) :=
  rule.consequence (fun _ _ _ hi => hi) (fun _ _ _ _ hi => hi.1)

private theorem result (value : α) : StatePrefixEnsures (Keep P) Safe (Pure.pure value) (fun _ h _ _ => Safe h) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi.1)

private theorem comparison (d : Decision) (b : Bool) (left right : Int) :
    StatePrefixEnsures (Keep P) Safe (liftWGPrefix (branchCmp d b left right))
      (fun x => Keep (fun h => P h ∧ x = b)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w a x v b hi run
  cases run
  exact ⟨hi.1,hi.2,rfl⟩

private theorem selection (pid : PeerId) : Driver.StateHistorySafe Safe (Journal.selection pid) := by
  apply (quiet (P := fun _ => True) (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl)
      ((HandshakeSecurity.Responder.DriverCuts.selection pid).run w)) (fun _ _ _ _ => trivial)).consequence
  · exact fun _ _ _ hi => ⟨hi,trivial⟩
  · exact fun _ _ _ _ hi => hi.1

private theorem creation (pid : PeerId) (items : List SkbId) :
    Driver.StateHistorySafe Safe (Journal.create pid items) := by
  have appends : StateAppends (Journal.create pid items) := by
    intro w a h
    exact Appends.focus Journal.Event.disposition Journal.disposition? (TxDisposition.create pid items)
      (NativeAdapter.world w a) h
  have unchanged : StateHistoryFrame ReservationHistory.allocation? (Journal.create pid items) := by
    intro w a h
    exact focusPrefix_other Journal.Event.disposition Journal.disposition? ReservationHistory.allocation?
      (fun _ => rfl) (TxDisposition.create pid items) (NativeAdapter.world w a) h
  exact (quiet (P := fun _ => True) appends unchanged (fun _ _ _ _ => trivial)).consequence
    (fun _ _ _ hi => ⟨hi,trivial⟩) (fun _ _ _ _ hi => hi.1)

theorem staging (pid : PeerId) : Driver.StateHistorySafe Safe (Driver.stagingObserved Journal.hooks pid) := by
  unfold Driver.stagingObserved
  simp only [Driver.restore_noKey_lift Journal.hooks rfl rfl rfl]
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (selection pid)
  intro chosen
  cases chosen with
  | none => exact Driver.History.state_pure _
  | some pair =>
    obtain ⟨p,kp⟩ := pair
    apply StatePrefixEnsures.bind (Driver.History.state_lift _)
    intro missing
    split
    · exact Driver.History.state_lift _
    · cases kp with
      | none => exact Driver.History.state_lift _
      | some id =>
        apply StatePrefixEnsures.bind (Driver.History.state_lift _)
        intro key
        apply StatePrefixEnsures.bind (Driver.History.state_lift _)
        intro invalid
        split
        · exact Driver.History.state_lift _
        · apply StatePrefixEnsures.bind (Driver.History.state_lift _)
          intro expired
          split
          · exact Driver.History.state_lift _
          · apply StatePrefixEnsures.consequence
              (P := Keep (fun h => Packets h [])) (Q := fun _ h _ _ => Safe h)
            · apply StatePrefixEnsures.bind (Q := fun acc : Option Unit × List DataPacket =>
                  Keep (fun h => Packets h acc.2))
              · apply StatePrefixEnsures.forInInvariant p.staged (none, []) _
                  (fun acc : Option Unit × List DataPacket => Keep (fun h => Packets h acc.2)) Safe
                  (fun _ _ _ _ hi => hi.1)
                intro pkt acc
                apply StatePrefixEnsures.bind (lift _)
                intro _
                apply StatePrefixEnsures.bind (lift _)
                intro ds
                apply StatePrefixEnsures.bind (reserve id acc.2)
                intro nonce
                apply StatePrefixEnsures.bind (comparison _ _ _ _)
                intro rejected
                cases rejected with
                | true =>
                  apply StatePrefixEnsures.bind (lift _)
                  intro out
                  apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
                  intro h w a hi
                  exact ⟨hi.1,hi.2.1.old⟩
                | false =>
                  apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
                  intro h w a hi
                  exact ⟨hi.1,hi.2.1.append (DataPacket.mk pid id nonce pkt ds .uncrypted []) rfl rfl⟩
              · intro acc
                obtain ⟨done,packets⟩ := acc
                cases done with
                | some out => exact result _
                | none =>
                  apply StatePrefixEnsures.bind (lift _)
                  intro _
                  apply StatePrefixEnsures.bind (lift _)
                  intro owner
                  apply StatePrefixEnsures.bind (lift _)
                  intro _
                  exact StatePrefixEnsures.bind (allocate packets) (fun items => creation pid items)
            · intro h w a hi
              exact ⟨hi,Packets.empty⟩
            · exact fun _ _ _ _ hi => hi

end Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
