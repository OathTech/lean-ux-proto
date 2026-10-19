import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral
import Leanux.Proofs.WG.TransmitSecurity.BatchPayloadSource
import Leanux.Proofs.WG.TransmitSecurity.StagingProcessed

/-! Native staging transports the selected plaintext sequence into the exact
allocation batch. Failed traversal has a separate, non-allocating exit. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchPayload
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem forget {g : WGPrefix Journal.Event α} (rule : StatePrefixPreserves (Keep P) Safe g) :
    StatePrefixEnsures (Keep P) Safe g (fun _ h _ _ => Safe h) :=
  rule.consequence (fun _ _ _ hi => hi) (fun _ _ _ _ hi => hi.1)

private theorem result (value : α) : StatePrefixEnsures (Keep P) Safe (Pure.pure value) (fun _ h _ _ => Safe h) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi.1)

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


private def Loop (pid : PeerId) (peer : Peer) (slot : KeypairId)
    (seen : List Packet) (acc : Option Unit × List DataPacket) :=
  Keep (fun h => Selected h pid peer slot ∧ acc.1 = none ∧ Shape pid slot seen acc.2)

private def Done (acc : Option Unit × List DataPacket) (h : List Journal.Event)
    (_ : WGWorld) (_ : Ambient) := Safe h ∧ acc.1.isSome = true

theorem staging (pid : PeerId) : Driver.StateHistorySafe Safe (Driver.stagingObserved Journal.hooks pid) := by
  unfold Driver.stagingObserved
  simp only [Driver.noKey_lift Journal.hooks rfl]
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (selection pid)
  intro chosen
  cases chosen with
  | none => exact result _
  | some pair =>
    obtain ⟨p,kp⟩ := pair
    apply StatePrefixEnsures.bind (lift _)
    intro missing
    split
    · exact forget (lift _)
    · cases kp with
      | none => exact forget (lift _)
      | some id =>
        apply StatePrefixEnsures.bind (lift _)
        intro key
        apply StatePrefixEnsures.bind (lift _)
        intro invalid
        split
        · exact forget (lift _)
        · apply StatePrefixEnsures.bind (lift _)
          intro expired
          split
          · exact forget (lift _)
          · apply StatePrefixEnsures.consequence
              (P := Loop pid p id [] (none,[])) (Q := fun _ h _ _ => Safe h)
            · apply StatePrefixEnsures.bind
              · apply forIn_processed p.staged [] (none,[]) _ (Loop pid p id) Done Safe
                  (fun _ _ _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi.1)
                intro pkt seen acc
                apply StatePrefixEnsures.bind (lift _)
                intro _
                apply StatePrefixEnsures.bind (lift _)
                intro ds
                apply StatePrefixEnsures.bind (reserve id (by
                  intro h later included hi
                  exact ⟨hi.1.mono included,hi.2⟩))
                intro nonce
                apply StatePrefixEnsures.bind (lift _)
                intro rejected
                cases rejected with
                | true =>
                  apply StatePrefixEnsures.bind (lift _)
                  intro out
                  apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
                  intro h w a hi
                  exact ⟨hi.1,rfl⟩
                | false =>
                  apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
                  intro h w a hi
                  refine ⟨hi.1,hi.2.1,rfl,?_,?_⟩
                  · simp only [List.map_append,List.map_cons,List.map_nil]
                    exact congrArg (fun xs => xs ++ [pkt]) hi.2.2.2.1
                  · intro packet member
                    rcases List.mem_append.mp member with old | new
                    · exact hi.2.2.2.2 packet old
                    · have same : packet = DataPacket.mk pid id nonce pkt ds .uncrypted [] := by simpa using new
                      subst packet
                      exact ⟨rfl,rfl⟩
              · intro acc
                obtain ⟨done,packets⟩ := acc
                cases done with
                | some out =>
                  apply StatePrefixEnsures.pure _
                  · intro h w a hi; exact hi.elim (fun x => x.1) (fun x => x.1)
                  · intro h w a hi; exact hi.elim (fun x => x.1) (fun x => x.1)
                | none =>
                  apply StatePrefixEnsures.consequence (P := Keep (fun h => Source h packets))
                    (Q := fun _ h _ _ => Safe h)
                  · apply StatePrefixEnsures.bind (lift _)
                    intro _
                    apply StatePrefixEnsures.bind (lift _)
                    intro owner
                    apply StatePrefixEnsures.bind (lift _)
                    intro _
                    exact StatePrefixEnsures.bind (allocate packets) (fun items => creation pid items)
                  · intro h w a hi
                    rcases hi with done | complete
                    · simp [Done] at done
                    · exact ⟨complete.1,pid,p,id,complete.2.1,complete.2.2.2⟩
                  · exact fun _ _ _ _ hi => hi
            · intro h w a hi
              exact ⟨hi.1,hi.2 p id rfl,rfl,rfl,by intro packet member; cases member⟩
            · exact fun _ _ _ _ hi => hi

end Leanux.Proofs.WG.TransmitSecurity.BatchPayload
