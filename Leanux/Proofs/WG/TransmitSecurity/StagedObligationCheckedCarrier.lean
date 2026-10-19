import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreEntrySource
import Leanux.Proofs.WG.TransmitSecurity.BatchPayloadHistory
import Leanux.Proofs.WG.TransmitSecurity.StagingProcessed

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.CheckedCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects CausalJournal

private theorem preserve_fact {Safe : List Event → Prop}
    (rule : StatePrefixPreserves P Safe action) (fact : Prop) :
    StatePrefixPreserves (fun h w a => P h w a ∧ fact) Safe action := by
  intro w a h before
  obtain ⟨suffix,position,safe,after⟩ := rule w a h before.1
  refine ⟨suffix,position,safe,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [outcome] using after,before.2⟩

private def Loop (P : List Event → WGWorld → Ambient → Prop) (pid : PeerId) (slot : KeypairId)
    (seen : List Packet) (acc : Option Unit × List DataPacket)
    (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  P h w a ∧ acc.1 = none ∧ BatchPayload.Shape pid slot seen acc.2

private def Done (Post : List Event → WGWorld → Ambient → Prop)
    (acc : Option Unit × List DataPacket) (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  Post h w a ∧ acc.1.isSome = true

/-- The original checked-send source composes local native leaf contracts
and gives submission its exact ordered plaintext/peer/key batch. The caller
chooses the carrier and stopped safety property; no callback or containing-run
success is inferred here. -/
theorem checked (P : List Event → WGWorld → Ambient → Prop)
    (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) (Safe : List Event → Prop)
    (safeP : ∀ h w a, P h w a → Safe h)
    (ambient : ∀ {α} (action : AmbientM α), StatePrefixPreserves P Safe
      (liftWGPrefix (monadLift action : WG.M α)))
    (world : ∀ {α} (action : WG.M α), SameView id action → StatePrefixPreserves P Safe (liftWGPrefix action))
    (readKey : ∀ kid, StatePrefixPreserves P Safe (liftWGPrefix (getKeypair kid)))
    (reserve : ∀ kid, StatePrefixPreserves P Safe (state (Journal.reserve kid)))
    (Post : List Event → WGWorld → Ambient → Prop)
    (postSafe : ∀ h w a, Post h w a → Safe h)
    (noKey : Option KeypairId → Bool → WGPrefix Event Unit)
    (submit : KeypairId → List DataPacket → WGPrefix Event Unit)
    (rejected : ∀ kp invalid, StatePrefixEnsures (P) Safe
      (noKey kp invalid) (fun _ => Post))
    (submitted : ∀ kid packets, StatePrefixEnsures
      (fun h w a => P h w a ∧
        BatchPayload.Shape pid kid peer.staged packets) Safe (submit kid packets) (fun _ => Post)) :
    StatePrefixEnsures (P) Safe
      (RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid)) noKey submit pid peer keypair)
      (fun _ => Post) := by
  unfold RestoreEntry.checkedWith
  apply StatePrefixEnsures.bind (ambient (AmbientM.branch .stagedNoKeypair keypair.isNone))
  intro missing
  split
  · exact rejected keypair false
  · cases keypair with
    | none =>
      apply StatePrefixEnsures.lift _ (fun _ _ _ before => safeP _ _ _ before)
      intro h w a value v b before run
      cases run
    | some id =>
      apply StatePrefixEnsures.bind (readKey id)
      intro key
      apply StatePrefixEnsures.bind (ambient (AmbientM.branch .stagedKeyInvalid !key.sending.isValid))
      intro invalid
      split
      · exact rejected (some id) false
      · apply StatePrefixEnsures.bind (world _ (branchExpired_sameWGWorld _ _ _ _))
        intro expired
        split
        · exact rejected (some id) true
        · apply StatePrefixEnsures.consequence
            (P := Loop P pid id [] (none,[]))
            (Q := fun _ => Post)
          · apply StatePrefixEnsures.bind
            · apply forIn_processed peer.staged [] (none,[]) _
                (Loop P pid id) (Done Post) Safe
                (fun _ _ _ _ _ before => safeP _ _ _ before.1)
                (fun _ _ _ _ before => postSafe _ _ _ before.1)
              intro packet seen acc
              apply StatePrefixEnsures.bind (preserve_fact
                (ambient (AmbientM.branch .stagedNonceIterate true)) _)
              intro _
              apply StatePrefixEnsures.bind (preserve_fact
                (world _ (ipTunnelEcnEncap_sameWGWorld packet)) _)
              intro ds
              apply StatePrefixEnsures.bind (preserve_fact (reserve id) _)
              intro nonce
              apply StatePrefixEnsures.bind (preserve_fact (ambient
                (AmbientM.branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES)) _)
              intro over
              cases over with
              | true =>
                apply StatePrefixEnsures.bind ((rejected (some id) true).consequence
                  (fun _ _ _ before => before.1) (fun _ _ _ _ after => after))
                intro out
                exact StatePrefixEnsures.pure _ (fun _ _ _ before => postSafe _ _ _ before)
                  (fun _ _ _ before => ⟨before,rfl⟩)
              | false =>
                apply StatePrefixEnsures.pure _ (fun _ _ _ before => safeP _ _ _ before.1)
                intro h w a before
                refine ⟨before.1,rfl,?_,?_⟩
                · simp only [List.map_append,List.map_cons,List.map_nil]
                  exact congrArg (fun xs => xs ++ [packet]) before.2.2.1
                · intro input member
                  rcases List.mem_append.mp member with old | new
                  · exact before.2.2.2 input old
                  · have same : input = DataPacket.mk pid id nonce packet ds .uncrypted [] := by simpa using new
                    subst input
                    exact ⟨rfl,rfl⟩
            · intro acc
              obtain ⟨done,packets⟩ := acc
              cases done with
              | some out =>
                apply StatePrefixEnsures.pure _
                  (fun _ _ _ before => before.elim
                    (fun h => postSafe _ _ _ h.1) (fun h => safeP _ _ _ h.1))
                intro h w a before
                rcases before with done | continuing
                · exact done.1
                · cases continuing.2.1
              | none =>
                apply StatePrefixEnsures.consequence
                  (P := fun h w a => P h w a ∧
                    BatchPayload.Shape pid id peer.staged packets) (Q := fun _ => Post)
                · exact StatePrefixEnsures.bind (preserve_fact
                    (ambient (AmbientM.branch .stagedNonceIterate false)) _)
                    (fun _ => submitted id packets)
                · intro h w a before
                  rcases before with finished | held
                  · simp [Done] at finished
                  · exact ⟨held.1,by simpa only [List.nil_append] using held.2.2⟩
                · exact fun _ _ _ _ after => after
          · intro h w a before
            exact ⟨before,rfl,rfl,by intro packet member; cases member⟩
          · exact fun _ _ _ _ after => after

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.CheckedCarrier
