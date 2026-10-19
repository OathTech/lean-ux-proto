import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCryptSources
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixIngress
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProduct
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteExecutionSources

/-! Concrete source-prefix certificates and native allocation companions
are joined on the same original action. Endpoint erasure supplies only the
allocation companion, never a prefix certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal

theorem poll : Checked hooks.poll :=
  pair_product (Crypt.poll CompleteProduct.Safe CompleteProduct.account_safe) CompleteProduct.poll

theorem encrypt (item : Option (List SkbId)) : Checked (hooks.encrypt item) :=
  pair_product (Crypt.encrypt CompleteProduct.Safe CompleteProduct.account_safe item) (CompleteProduct.encrypt item)

theorem prepare : Checked hooks.prepare :=
  pair_product (Crypt.prepare CompleteProduct.Safe CompleteProduct.account_safe) CompleteProduct.prepare

theorem received (msg : Key) (src : SkbSource) : Checked (Driver.receiveEntryObserved hooks msg src) :=
  pair_product (Ingress.checked CompleteProduct.Safe CompleteProduct.account_safe msg src)
    (CompleteProduct.Execution.received msg src)

theorem staging (pid : PeerId) : StateChecked (Driver.stagingObserved hooks pid) :=
  pair (Staging.staging [] [] pid) (CompleteProduct.staging pid)

theorem release (peer : Option PeerId) : StateChecked (hooks.peerRelease peer) :=
  pair (Disposal.original peer CompleteProduct.Safe CompleteProduct.account_safe) (CompleteProduct.release peer)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
