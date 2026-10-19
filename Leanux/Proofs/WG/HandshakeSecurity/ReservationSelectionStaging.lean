import Leanux.Proofs.WG.HandshakeSecurity.ReservationSelectionSource
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral

/-! The exact native staging loop connects every reservation to its selected
current key. Refusal may remove a key, so transport uses only surviving cores. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReservationSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem ambient (action : AmbientM α) :
    StatePrefixPreserves (Keep (fun h w => Picked h slot w)) Safe
      (liftWGPrefix (monadLift action)) :=
  lift _ (ResidentMaterial.core_of_same (by intro initial; exact hoare_liftAmbient _ _))

private theorem allocate (packets : List DataPacket) : Driver.StateHistorySafe Safe (Journal.allocate packets) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))

private theorem creation (pid : PeerId) (items : List SkbId) :
    Driver.StateHistorySafe Safe (Journal.create pid items) := by
  have appends : StateAppends (Journal.create pid items) := by
    intro w a h
    exact Appends.focus Journal.Event.disposition Journal.disposition? (TxDisposition.create pid items)
      (NativeAdapter.world w a) h
  have unchanged : StateHistoryFrame reservation? (Journal.create pid items) := by
    intro w a h
    exact focusPrefix_other Journal.Event.disposition Journal.disposition? reservation?
      (fun _ => rfl) (TxDisposition.create pid items) (NativeAdapter.world w a) h
  exact state_quiet appends unchanged

private theorem forget {g : WGPrefix Journal.Event α} (safe : Driver.StateHistorySafe Safe g) :
    StatePrefixEnsures (Keep P) Safe g (fun _ h _ _ => Safe h) :=
  safe.consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

theorem staging (pid : PeerId) : Driver.StateHistorySafe Safe (Driver.stagingObserved Journal.hooks pid) := by
  unfold Driver.stagingObserved
  simp only [Driver.noKey_lift Journal.hooks rfl]
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (selection pid)
  intro chosen
  cases chosen with
  | none => exact (Driver.History.state_pure _).consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)
  | some pair =>
    obtain ⟨peer,kp⟩ := pair
    cases kp with
    | none =>
      apply StatePrefixEnsures.consequence (P := fun h _ _ => Safe h) (Q := fun _ h _ _ => Safe h)
      · apply StatePrefixEnsures.bind (Driver.History.state_lift _)
        intro missing
        split <;> exact Driver.History.state_lift _
      · exact fun _ _ _ hi => hi.1
      · exact fun _ _ _ _ hi => hi
    | some kid =>
      apply StatePrefixEnsures.consequence (P := Keep (fun h w => Picked h kid w)) (Q := fun _ h _ _ => Safe h)
      · apply StatePrefixEnsures.bind (ambient _)
        intro missing
        split
        · exact forget (Driver.History.state_lift _)
        · apply StatePrefixEnsures.bind (lift _ (ResidentMaterial.core_of_same
            (pool_of_material (Origins.Retaining.getKeypair_material kid))))
          intro key
          apply StatePrefixEnsures.bind (ambient _)
          intro invalid
          split
          · exact forget (Driver.History.state_lift _)
          · apply StatePrefixEnsures.bind (lift _ (ResidentMaterial.core_of_same
              ((branchExpired_sameWGWorld _ _ _ _).factor pool)))
            intro expired
            split
            · exact forget (Driver.History.state_lift _)
            · apply StatePrefixEnsures.bind (Q := fun _ => Keep (fun h w => Picked h kid w))
              · apply StatePrefixEnsures.forInInvariant peer.staged (none, []) _
                  (fun _ => Keep (fun h w => Picked h kid w)) Safe (fun _ _ _ _ hi => hi.1)
                intro pkt acc
                apply StatePrefixEnsures.bind (ambient _)
                intro _
                apply StatePrefixEnsures.bind (lift _ (ResidentMaterial.core_of_same
                  ((ipTunnelEcnEncap_sameWGWorld pkt).factor pool)))
                intro ds
                apply StatePrefixEnsures.bind (reserve kid)
                intro nonce
                apply StatePrefixEnsures.bind (ambient _)
                intro rejected
                split
                · apply StatePrefixEnsures.bind (lift _ (stagedOutNokey_core pid peer.staged (some kid) true))
                  intro out
                  exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
                · exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
              · intro acc
                obtain ⟨done,packets⟩ := acc
                cases done with
                | some out => exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi.1)
                | none =>
                  apply StatePrefixEnsures.consequence (P := fun h _ _ => Safe h) (Q := fun _ h _ _ => Safe h)
                  · apply StatePrefixEnsures.bind (Driver.History.state_lift _)
                    intro _
                    apply StatePrefixEnsures.bind (Driver.History.state_lift _)
                    intro owner
                    apply StatePrefixEnsures.bind (Driver.History.state_lift _)
                    intro _
                    exact StatePrefixEnsures.bind (allocate packets) (fun items => creation pid items)
                  · exact fun _ _ _ hi => hi.1
                  · exact fun _ _ _ _ hi => hi
      · exact fun _ _ _ hi => ⟨hi.1,hi.2 peer kid rfl⟩
      · exact fun _ _ _ _ hi => hi

end Leanux.Proofs.WG.HandshakeSecurity.ReservationSelection
