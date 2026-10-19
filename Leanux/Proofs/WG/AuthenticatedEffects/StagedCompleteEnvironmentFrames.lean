import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeferredFrames

/-! Administrative environment frames retain the same paired packet ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal

theorem idle_device : Checked (liftPrefix Env.requireIdleDevice) :=
  product_store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store)

theorem inetdev : Checked (liftPrefix Env.inetdevDestroy) :=
  product_store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.inetdevDestroy_store)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
