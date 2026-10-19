import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityRoutingObserved
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityStaging
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityActualFrames
import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableRouting
import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableKeepalive

/-! Native staging consumes each saved live batch on allocation; all refusal
arms restore its existing credits. These are incoming-carrier source contracts. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000

theorem queued_observed (pid : PeerId) (retry : Bool) :
    StateSafe (TimerEffects.queuedWith effects pid retry) :=
  state_quiet (Origins.queued_appends pid retry)
    (TimerEffects.queued_frame allocation?
      (CausalEffects.ops_frames scope? Event.armed Event.queued allocation? (fun _ => rfl) (fun _ => rfl)) pid retry)
    (TimerEffects.queued_erases (CausalEffects.ops_erases scope? Event.armed Event.queued) pid retry)
    (fun _ => Native.queued pid retry)

theorem queued_actual (pid : PeerId) (retry : Bool) :
    StateSafe (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid retry) := by
  have quiet := CallbackQuiet.queued allocation? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid retry
  exact state_quiet quiet.1 quiet.2 (queued_actual_erases pid retry) (fun _ => Native.queued pid retry)

theorem held_pure (value : α) : StatePrefixPreserves (Held pid peer) Safe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ before => before.1.2) (fun _ _ _ before => before)

theorem held_loop {α β : Type} (xs : List α) (initial : β)
    (body : α → β → WGPrefix Event (ForInStep β))
    (step : ∀ x b, StatePrefixPreserves (Held pid peer) Safe (body x b)) :
    StatePrefixPreserves (Held pid peer) Safe (forIn xs initial body) :=
  StatePrefixEnsures.forInInvariant xs initial body (fun _ => Held pid peer) Safe
    (fun _ _ _ _ before => before.1.2) step

theorem no_key_observed (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) (invalid : Bool) :
    StatePrefixEnsures (Held pid peer) Safe
      (HandshakeSecurity.StagedConservation.Restore.noKeyWith effects stagedRestore
        (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease) pid peer.staged keypair invalid)
      (fun _ h w _ => Carrier h w) := by
  have tail (kp : Option KeypairId) : StatePrefixEnsures (Held pid peer) Safe
      (do
        effects.step (keypairPut kp false)
        for _ in peer.staged do _ ← effects.step (branch .stagedOrphanWalk true)
        _ ← effects.step (branch .stagedOrphanWalk false)
        stagedRestore pid peer.staged
        HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false)
      (fun _ h w _ => Carrier h w) := by
    apply StatePrefixEnsures.bind (held_key_put kp false)
    intro _
    apply StatePrefixEnsures.bind
    · apply held_loop
      intro packet acc
      apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedOrphanWalk true))
      intro _
      exact held_pure _
    · intro _
      apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedOrphanWalk false))
      intro _
      exact StatePrefixEnsures.bind (restore_actual pid peer) (fun _ => queued_actual pid false)
  unfold HandshakeSecurity.StagedConservation.Restore.noKeyWith
  dsimp only
  split
  · split
    · apply StatePrefixEnsures.bind (held_read_key _)
      intro key
      exact StatePrefixEnsures.bind (held_write_key _ _) (fun _ => tail _)
    · exact StatePrefixEnsures.bind (held_ambient (AmbientM.invariant "unreachable")) (fun _ => tail _)
  · exact tail _

theorem create_observed (pid : PeerId) (items : List SkbId) : StateSafe (CausalJournal.create pid items) := by
  have quiet := CallbackQuiet.create allocation? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid items
  exact state_quiet quiet.1 quiet.2 (create_actual_erases pid items) (fun _ => Native.create pid items)

theorem staging_observed (pid : PeerId) : StateSafe (Driver.stagingObserved hooks pid) :=
  staging_source no_key_observed create_observed pid

theorem routing_observed (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (state (Journal.front family addr packets mtu)) := by
  unfold state Journal.front
  rw [Origins.focused_native_receipt]
  intro w a h before
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (Packets.txFront family addr packets mtu))
    (Event.old ∘ Journal.Event.routed family addr packets mtu) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((Packets.txFront family addr packets mtu).run w).run a with
  | error stop => exact ⟨[],by simp,before.2,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let receipt : Journal.RoutingHistory.Receipt := ⟨family,addr,packets,mtu,⟨value,w,v,a,b⟩⟩
    have safe : Safe (h ++ [.old (.routed family addr packets mtu receipt.run)]) := before.2.emit True.intro
    refine ⟨[.old (.routed family addr packets mtu receipt.run)],rfl,safe,?_,safe⟩
    cases value with
    | error err => exact (routing_failure receipt run err rfl before.1).append (quiet_singleton rfl)
    | ok pid => exact routing_success receipt run pid rfl before.1

theorem keepalive_observed (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Carrier h w) Safe
      (AuthenticatedEffects.CausalJournal.keepalivePrepare pid) := by
  intro w a h before
  unfold AuthenticatedEffects.CausalJournal.keepalivePrepare
  have equation := runWGPrefix_receiptWGObserved
    (liftWGPrefix (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
    (Event.keepalivePrepared pid) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid).run w).run a with
  | error stop => exact ⟨[],by simp,before.2,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let receipt : WGRunWitness Bool := ⟨value,w,v,a,b⟩
    have safe : Safe (h ++ [.keepalivePrepared pid receipt]) := before.2.emit True.intro
    exact ⟨[.keepalivePrepared pid receipt],rfl,safe,
      keepalive_inv pid receipt run before.1,safe⟩

theorem keepalive_observed_source (pid : PeerId) : StateSafe (Driver.keepaliveObserved hooks pid) := by
  unfold Driver.keepaliveObserved
  apply StatePrefixEnsures.bind (keepalive_observed pid)
  intro ready
  cases ready
  · exact state_pure _
  · exact staging_observed pid

theorem transmit_observed (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  apply StatePrefixEnsures.bind (routing_rich family addr packets mtu)
  intro selected
  cases selected with
  | error err => exact state_pure err
  | ok pid =>
    apply StatePrefixEnsures.bind (staging_observed pid)
    intro _
    exact StatePrefixEnsures.bind (peer_release_observed (some pid)) (fun _ => state_pure 0)


end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
