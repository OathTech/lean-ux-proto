import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldFrontierFrames

/-! The native key borrow and no-key prefix preserve the same selected batch,
all other fixed obligations and physical cleanup backing. Their stopped
history still names the active take cut, not merely a prior terminal record. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Staged.Origins AuthenticatedEffects CausalJournal
open HandshakeSecurity.StagedConservation

theorem borrow_held (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (Safe : List Event → Prop)
    (frontier : ∀ h, Anchor ledger debts generation pid peer position h → Safe h) :
    StatePrefixEnsures (Held ledger debts generation pid peer position) Safe
      (liftWGPrefix (Take.borrow (some peer)))
      (fun selected h w a => ∃ keypair, selected = some (peer,keypair) ∧
        Held ledger debts generation pid peer position h w a) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => frontier _ before.anchor)
  intro h w a chosen v b before run
  unfold Take.borrow at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨keypair,u,c,borrowed,returned⟩ := run
  have epoch := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire peer.keypairCurrent).factor Prod.fst))
    w a keypair u c borrowed
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp (key_get_staged peer.keypairCurrent)
    w a keypair u c borrowed
  have cells := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PacketMaterial.of_packets ((RetirementSecurity.keyGet_cryptWire peer.keypairCurrent).factor Prod.snd))
    w a keypair u c borrowed
  have kept : Held ledger debts generation pid peer position h u c := by
    simpa only [List.append_nil] using before.views_append (b := c) [] (by simp) epoch queues cells
  simp only [StateT.run_pure,CounterWindow.except_pure,Except.ok.injEq,Prod.mk.injEq] at returned
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := returned
  exact ⟨keypair,rfl,kept⟩

theorem prefix_held (Safe : List Event → Prop)
    (frontier : ∀ h, Anchor ledger debts generation pid peer position h → Safe h)
    (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StatePrefixPreserves (Held ledger debts generation pid peer position) Safe
      (RestoreEntry.prefixWith liftWGPrefix packets keypair invalid) := by
  have tail (kp : Option KeypairId) :
      StatePrefixPreserves (Held ledger debts generation pid peer position) Safe (do
        liftWGPrefix (keypairPut kp false)
        for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
        _ ← liftWGPrefix (branch .stagedOrphanWalk false)) := by
    apply StatePrefixEnsures.bind (held_key_put frontier kp)
    intro _
    apply StatePrefixEnsures.bind
    · apply StatePrefixEnsures.forInInvariant packets PUnit.unit _
        (fun _ => Held ledger debts generation pid peer position) Safe
        (fun _ _ _ _ before => frontier _ before.anchor)
      intro packet acc
      exact StatePrefixEnsures.bind (held_ambient frontier (AmbientM.branch .stagedOrphanWalk true))
        (fun _ => held_pure frontier _)
    · intro _
      exact StatePrefixEnsures.bind (held_ambient frontier (AmbientM.branch .stagedOrphanWalk false))
        (fun _ => held_pure frontier _)
  unfold RestoreEntry.prefixWith
  dsimp only
  split
  · split
    · apply StatePrefixEnsures.bind (held_read_key frontier _)
      intro key
      exact StatePrefixEnsures.bind (held_write_key frontier _ _) (fun _ => tail _)
    · exact StatePrefixEnsures.bind (held_ambient frontier (AmbientM.invariant "unreachable"))
        (fun _ => tail _)
  · exact tail _

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
