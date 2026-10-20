import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIngressCanonical

/-! Native ingress and counted release normal endpoints supply the same
complete account and allocation companion to their actual next bind. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

theorem Shape.checked (source : Shape action) : CompleteProduct.Checked action := by
  induction source with
  | pure value=>exact CompleteProduct.pure_checked value
  | native kind=>exact kind.checked
  | release peer=>
      exact CompleteProduct.state
        (CompleteDeviceConfiguration.release CompleteProduct.Safe CompleteProduct.account_safe peer)
  | bind head tail ihHead ihTail=>exact CompleteProduct.bind_checked ihHead ihTail

theorem Shape.normal (source : Shape action) (before : CompleteProduct.Carrier h w)
    (performed : runPrefix action w h=(.ok (value,u),middle)) : CompleteProduct.Carrier middle u :=
  Xmit.normal source.checked before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
