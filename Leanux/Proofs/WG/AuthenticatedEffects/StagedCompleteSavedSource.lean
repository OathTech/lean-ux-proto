import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySavedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePassive

/-! Saved metadata reads and writes retain Entry and receipt completeness on
one ledger. Intervening guards preserve the exact native peer fields. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSaved
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

def Saved (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (p : Peer) (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  CompleteCarrier.Carrier debts locals h w a ∧ SavedFrames.PeerFields pid p w

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem read (pid : PeerId) :
    StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe (liftWGPrefix (getPeer pid))
      (fun p => Saved debts locals pid p) := by
  apply StatePrefixEnsures.lift _
    (fun h w _ before => by obtain ⟨ledger,entry⟩ := before; exact accountSafe ledger h w entry)
  intro h w a p v b before run
  obtain ⟨same,_,d,device,resident⟩ := getPeer_normal pid w v p a b run
  subst v
  exact ⟨before,d,p,device,resident,rfl,rfl,rfl⟩

theorem store (pid : PeerId) (p : Peer) (action : WG.M α) (same : SameWGStore action) :
    StatePrefixPreserves (Saved debts locals pid p) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _
    (fun h w _ before => by obtain ⟨ledger,entry⟩ := before.1; exact accountSafe ledger h w entry)
  intro h w a value v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp same w a value v b run
  obtain ⟨ledger,entry⟩ := before.1
  refine ⟨⟨ledger,entry.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (TimerFrames.store same) w a value v b run)⟩,?_⟩
  have device := congrArg WGStoreView.dev fields
  change v.dev = w.dev at device
  simpa only [SavedFrames.PeerFields,device] using before.2

theorem write (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue) :
    StatePrefixEnsures (Saved debts locals pid p) Safe (liftWGPrefix (setPeer pid (f p)))
      (fun _ => CompleteCarrier.Carrier debts locals) := by
  apply StatePrefixEnsures.lift _
    (fun h w _ before => by obtain ⟨ledger,entry⟩ := before.1; exact accountSafe ledger h w entry)
  intro h w a value v b before run
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (SavedFrames.write_saved pid p (f p) (· = StagedEntry.view w) (same p))
    w a value v b ⟨rfl,before.2⟩ run
  obtain ⟨ledger,entry⟩ := before.1
  exact ⟨ledger,entry.same_view kept.1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSaved
