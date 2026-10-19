import Leanux.Proofs.WG.HandshakeSecurity.StagingMaterialHistory
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral

/-! The complete shared native staging path certifies the reservation material
at every packet allocation. Failed guards retain earlier checks without
assuming that the released key remains resident. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem result (value : α) : StatePrefixEnsures (Keep P) Safe (Pure.pure value)
    (fun _ h _ _ => Safe h) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi.1)

private theorem ambient (action : AmbientM α) :
    StatePrefixPreserves (Keep (fun h w => Packets h packets w)) Safe
      (liftWGPrefix (monadLift action)) :=
  lift _ (ResidentMaterial.core_of_same (by intro initial; exact hoare_liftAmbient _ _))

private theorem comparison (d : Decision) (b : Bool) (left right : Int) :
    StatePrefixEnsures (Keep P) Safe (liftWGPrefix (branchCmp d b left right))
      (fun x => Keep (fun h w => P h w ∧ x = b)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w a x v b hi run
  cases run
  exact ⟨hi.1,hi.2,rfl⟩

private theorem selection (pid : PeerId) : Driver.StateHistorySafe Safe (Journal.selection pid) :=
  state_focus _ _ (fun _ => rfl) _

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
  exact state_quiet appends unchanged

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
              (P := Keep (fun h w => Packets h [] w)) (Q := fun _ h _ _ => Safe h)
            · apply StatePrefixEnsures.bind (Q := fun acc : Option Unit × List DataPacket =>
                  Keep (fun h w => Packets h acc.2 w))
              · apply StatePrefixEnsures.forInInvariant p.staged (none, []) _
                  (fun acc : Option Unit × List DataPacket => Keep (fun h w => Packets h acc.2 w)) Safe
                  (fun _ _ _ _ hi => hi.1)
                intro pkt acc
                apply StatePrefixEnsures.bind (ambient _)
                intro _
                apply StatePrefixEnsures.bind
                  (lift _ (ResidentMaterial.core_of_same ((ipTunnelEcnEncap_sameWGWorld pkt).factor pool)))
                intro ds
                apply StatePrefixEnsures.bind (reserve id acc.2)
                intro nonce
                apply StatePrefixEnsures.bind (comparison _ _ _ _)
                intro rejected
                cases rejected with
                | true =>
                  apply StatePrefixEnsures.bind (Q := fun _ => Keep (fun h w => Packets h acc.2 w))
                  · apply (lift _ (stagedOutNokey_core pid p.staged (some id) true)).consequence
                      (fun _ _ _ hi => ⟨hi.1,hi.2.1.old⟩) (fun _ _ _ _ hi => hi)
                  · intro out
                    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
                | false =>
                  apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
                  intro h w a hi
                  exact ⟨hi.1,hi.2.1.append (DataPacket.mk pid id nonce pkt ds .uncrypted []) rfl rfl⟩
              · intro acc
                obtain ⟨done,packets⟩ := acc
                cases done with
                | some out => exact result _
                | none =>
                  apply StatePrefixEnsures.bind (ambient _)
                  intro _
                  apply StatePrefixEnsures.bind
                    (lift _ (ResidentMaterial.core_of_same (pool_of_material (Origins.Retaining.ownerDeref_material _))))
                  intro owner
                  apply StatePrefixEnsures.bind
                    (lift _ (ResidentMaterial.core_of_same (pool_of_material (Origins.Retaining.peerGet_material _))))
                  intro _
                  exact StatePrefixEnsures.bind (allocate packets) (fun items => creation pid items)
            · intro h w a hi
              exact ⟨hi,Packets.empty⟩
            · exact fun _ _ _ _ hi => hi

end Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
