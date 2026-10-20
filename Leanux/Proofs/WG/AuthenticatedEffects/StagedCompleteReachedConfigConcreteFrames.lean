import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigConcreteCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigSavedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigRemovalFrames

/-! Configuration normal returns retain the initialized allocation companion
beside the complete packet ledger. Child interiors have separate source proofs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

theorem Family.checked (family : Family) : CompleteProduct.Checked family.action := by
  cases family with
  | release peer=>
      exact CompleteProduct.state
        (CompleteDeviceConfiguration.release CompleteProduct.Safe CompleteProduct.account_safe peer)
  | remove peer=>exact CompleteProduct.state (CompleteProduct.remove peer)
  | removeAll=>exact CompleteProduct.state CompleteProduct.remove_all
  | staging trigger pid=>
      exact CompleteProduct.state (CompleteProduct.fixture _ _ (CompleteProduct.staging pid))
  | keepalive trigger pid=>
      exact CompleteProduct.state (CompleteProduct.fixture _ _ (CompleteProduct.keepalive pid))

theorem Shape.checked (source : Shape action) : CompleteProduct.Checked action := by
  induction source with
  | pure value=>exact CompleteProduct.pure_checked value
  | native token=>exact token.checked
  | child family=>exact family.checked
  | saved pid running interval=>exact ConfigSaved.checked pid running interval
  | psk pid psk=>exact psk_checked pid psk
  | bind head tail ihHead ihTail=>exact CompleteProduct.bind_checked ihHead ihTail

theorem Shape.normal (source : Shape action) (before : CompleteProduct.Carrier h w)
    (performed : runPrefix action w h=(.ok (value,u),middle)) : CompleteProduct.Carrier middle u :=
  Xmit.normal source.checked before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
