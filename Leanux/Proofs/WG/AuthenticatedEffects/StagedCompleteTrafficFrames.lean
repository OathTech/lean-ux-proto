import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEnvironment
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedFixture

/-! Traffic wrapper frames and fixture markers retain the same complete
packet ledger; only the actual transmit body admits new tickets. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver

theorem multicast (family addr : Nat) : Checked (multicastObserved family addr) := by
  apply product_store
  intro initial
  change Framing.Preserves (fun w : World => productStoreView w = initial) _
  have loop : Framing.Preserves (fun w : World => productStoreView w = initial)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    liftWG_sameProductStore _ (loopbackSend_kernel [] true) initial
  have effects {α : Type} (a : AmbientM α) :
      Framing.Preserves (fun w : World => productStoreView w = initial) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ before => before)
  routing_tx_source [Env.xmitMulticastLoop] using [loop,effects]

theorem drain (what : String) (flags : List Bool) : Checked (drainObserved what flags) :=
  product_store _ (TransmitSecurity.Nonce.Frames.drained what flags)

theorem fixture (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α) (checked : StateChecked body) :
    StateChecked (FixtureEffects.runWith (fixtureOps hooks) trigger body) :=
  CompleteAllocatedFixture.run Safe account_safe trigger body checked

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
