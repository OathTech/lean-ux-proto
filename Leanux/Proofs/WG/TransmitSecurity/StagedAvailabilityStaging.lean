import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityRestore
import Leanux.Proofs.WG.TransmitSecurity.BatchPayloadHistory
import Leanux.Proofs.WG.TransmitSecurity.StagingProcessed

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem preserve_fact (rule : StatePrefixPreserves P Safe action) (fact : Prop) :
    StatePrefixPreserves (fun h w a => P h w a ∧ fact) Safe action := by
  intro w a h before
  obtain ⟨suffix,position,safe,after⟩ := rule w a h before.1
  refine ⟨suffix,position,safe,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [outcome] using after,before.2⟩

private def Loop (pid : PeerId) (peer : Peer) (slot : KeypairId)
    (seen : List Packet) (acc : Option Unit × List DataPacket) (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  Held pid peer h w a ∧ acc.1 = none ∧ BatchPayload.Shape pid slot seen acc.2

private def Done (acc : Option Unit × List DataPacket) (h : List Event) (w : WGWorld) (_ : Ambient) :=
  Carrier h w ∧ acc.1.isSome = true

private theorem forget_held {action : WGPrefix Event α}
    (safe : StatePrefixPreserves (Held pid peer) Safe action) :
    StatePrefixEnsures (Held pid peer) Safe action (fun _ h w _ => Carrier h w) :=
  safe.consequence (fun _ _ _ before => before) (fun _ _ _ _ after => after.1)

/-- Native control flow consumes a live saved batch only on its allocation
arm. Early no-key and counter-limit exits use their restoration contract. -/
theorem staging_source
    (noKey : ∀ pid peer key invalid, StatePrefixEnsures (Held pid peer) Safe
      (AuthenticatedEffects.PacketEffects.noKeyWith effects pid peer.staged key invalid)
      (fun _ h w _ => Carrier h w))
    (create : ∀ pid items, StateSafe (state (Journal.create pid items)))
    (pid : PeerId) : StateSafe (Driver.stagingObserved hooks pid) := by
  unfold Driver.stagingObserved
  apply StatePrefixEnsures.bind (selection_observed pid)
  intro chosen
  cases chosen with
  | none => exact StatePrefixEnsures.pure _ (fun _ _ _ before => before.1.2) (fun _ _ _ before => before.1)
  | some pair =>
    obtain ⟨p,kp⟩ := pair
    apply StatePrefixEnsures.consequence (P := Held pid p) (Q := fun _ h w _ => Carrier h w)
    · apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedNoKeypair kp.isNone))
      intro missing
      split
      · exact noKey pid p kp false
      · cases kp with
        | none => exact forget_held (held_ambient (AmbientM.invariant "unreachable"))
        | some id =>
          apply StatePrefixEnsures.bind (held_read_key id)
          intro key
          apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedKeyInvalid !key.sending.isValid))
          intro invalid
          split
          · exact noKey pid p (some id) false
          · apply StatePrefixEnsures.bind (held_world _ (branchExpired_sameWGWorld _ _ _ _))
            intro expired
            split
            · exact noKey pid p (some id) true
            · apply StatePrefixEnsures.consequence (P := Loop pid p id [] (none,[]))
                (Q := fun _ h w _ => Carrier h w)
              · apply StatePrefixEnsures.bind
                · apply forIn_processed p.staged [] (none,[]) _ (Loop pid p id) Done Safe
                    (fun _ _ _ _ _ before => before.1.1.2) (fun _ _ _ _ before => before.1.2)
                  intro packet seen acc
                  apply StatePrefixEnsures.bind (preserve_fact (held_ambient (AmbientM.branch .stagedNonceIterate true)) _)
                  intro _
                  apply StatePrefixEnsures.bind (preserve_fact (held_world _ (ipTunnelEcnEncap_sameWGWorld packet)) _)
                  intro ds
                  apply StatePrefixEnsures.bind (preserve_fact (reserve_observed id) _)
                  intro nonce
                  apply StatePrefixEnsures.bind (preserve_fact (held_ambient (AmbientM.branchCmp .stagedNonceRejected
                    (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES)) _)
                  intro rejected
                  cases rejected with
                  | true =>
                    apply StatePrefixEnsures.bind ((noKey pid p (some id) true).consequence
                      (fun _ _ _ before => before.1) (fun _ _ _ _ after => after))
                    intro out
                    exact StatePrefixEnsures.pure _ (fun _ _ _ before => before.2)
                      (fun _ _ _ before => ⟨before,rfl⟩)
                  | false =>
                    apply StatePrefixEnsures.pure _ (fun _ _ _ before => before.1.1.2)
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
                    exact StatePrefixEnsures.pure _
                      (fun _ _ _ before => before.elim (fun h => h.1.2) (fun h => h.1.1.2))
                      (fun _ _ _ before => before.elim (fun h => h.1) (fun h => h.1.1))
                  | none =>
                    apply StatePrefixEnsures.consequence (P := Allocating pid p packets)
                      (Q := fun _ h w _ => Carrier h w)
                    · apply StatePrefixEnsures.bind (preserve_fact (held_ambient (AmbientM.branch .stagedNonceIterate false)) _)
                      intro _
                      apply StatePrefixEnsures.bind (preserve_fact (held_world _
                        (fun initial => indexOwner_peerDeref_preserves (.keypair id) (fun w => w = initial))) _)
                      intro owner
                      apply StatePrefixEnsures.bind (preserve_fact (held_peer_get owner) _)
                      intro _
                      exact StatePrefixEnsures.bind (allocate_observed pid p packets) (fun items => create pid items)
                    · intro h w a before
                      rcases before with finished | held
                      · simp [Done] at finished
                      · exact ⟨held.1,by simpa only [List.nil_append] using held.2.2.1,
                          fun packet member => (held.2.2.2 packet member).1⟩
                    · exact fun _ _ _ _ after => after
              · intro h w a before
                exact ⟨before,rfl,rfl,by intro packet member; cases member⟩
              · exact fun _ _ _ _ after => after
    · intro h w a before
      exact ⟨before.1,before.2 p kp rfl⟩
    · exact fun _ _ _ _ after => after

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
