import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseNativeFrames

/-! The fixed ledger changes only at the actual final-release receipt.
Nonfinal repayment keeps it unchanged; final repayment settles exactly the
erased peer's staged tickets and keeps its allocated cells and cleanup debts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations QueueHandoff
set_option pp.structureInstances false

def Successor (value : Option (PeerId × Peer)) (before : WGWorld) (position : Nat)
    (ledger after : Ledger) : Prop :=
  match value with
  | none => after = ledger
  | some (pid,p) => ∃ generation, Packets.epoch before = some generation ∧
      after = settle (pendingAt (.staged generation pid p.internalId) ledger)
        (.counted position .finalRelease) ledger

/-- The native counted cut retains the same allocated obligations and owner
inventory. The only ledger transition is the precise staged final-release
settlement at its actual journal position, before the suffix can stop. -/
theorem cut_owned (peer : Option PeerId)
    (owned : Owned ledger debts locals history w) (bounded : Packets.Inv w.wg)
    (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),ambient),last)) :
    ∃ after, Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
      Successor value w.wg last.length ledger after ∧
      Owned after debts locals (last ++ [receipt peer value w.wg g w.ambient ambient])
        {w with wg := g,ambient := ambient} ∧ Packets.Inv g := by
  have native := cut_valid peer performed
  obtain ⟨suffix,extended,quiet⟩ := cut_birth_quiet peer w.wg w.ambient history
  rw [performed] at extended
  change last = history ++ suffix at extended
  have atEntry : Core last ledger debts w.wg := by
    rw [extended]
    exact owned.1.quiet_views suffix quiet rfl rfl rfl
  obtain ⟨covered,unique,bounds⟩ := cut_ownership peer owned.2.1 owned.2.2 bounded
    w.ambient ambient native
  cases value with
  | none =>
    refine ⟨ledger,Staged.Obligations.Step.refl _,AllocatedFrame.refl _,rfl,?_,bounds⟩
    exact ⟨core_release_none peer ⟨none,w.wg,g,w.ambient,ambient⟩ native rfl atEntry,covered,unique⟩
  | some pair =>
    obtain ⟨pid,p⟩ := pair
    obtain ⟨generation,epoch,step,core,_,_⟩ := core_release_final peer
      ⟨some (pid,p),w.wg,g,w.ambient,ambient⟩ native rfl atEntry
    have chosen : ∀ ticket ∈ pendingAt (.staged generation pid p.internalId) ledger,
        ticket ∈ pendingAt (.staged generation pid p.internalId) ledger := fun _ member => member
    have frame := settle_allocated_frame atEntry.valid chosen (by intro _ _; simp)
      (.counted last.length .finalRelease)
    exact ⟨_,step,frame,⟨generation,epoch,rfl⟩,⟨core,covered,unique⟩,bounds⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
