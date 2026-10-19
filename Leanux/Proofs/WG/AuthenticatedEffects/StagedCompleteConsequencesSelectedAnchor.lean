import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadySource

/-! A stopped selection retains the native queue/local ownership census at
its exact recorded take. This is a reached source cut, not a post-Stop world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open HandshakeSecurity.StagedConservation

def NativeAnchor (position : Nat) (history : List Event) : Prop :=
  ∃ (r : Take.Receipt) (locals : List TxLocalBatch),
    history[position]? = some (.stagingTaken r) ∧ NativeReady.Inv locals r.run.after

theorem NativeAnchor.here (r : Take.Receipt) (native : NativeReady.Inv locals r.run.after) :
    NativeAnchor history.length (history ++ [.stagingTaken r]) :=
  ⟨r,locals,by simp,native⟩


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
