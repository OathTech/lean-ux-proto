import Leanux.Proofs.WG.TransmitSecurity.StagedKeepalive
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptInitialized

/-! Actual keepalive preparation receipts in the initialized final journal.
This records a source operation; authorization of its cause is separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects.CausalJournal

theorem initialized_keepalive_preparation (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ Event.keepalivePrepared pid r :: post) :
    dropped r.after = dropped r.before ∧
      (∀ q, pid ≠ q → stagedAt r.after q = stagedAt r.before q) ∧
      ∃ stamp packets mtu,
        stagedAt r.before pid = some (stamp,packets) ∧
        r.before.dev.map Device.mtu = some mtu ∧
        (stagedAt r.after pid = some (stamp,packets) ∨
          (packets = [] ∧ r.value = true ∧ stagedAt r.after pid = some (stamp,[{mtu}]))) :=
  keepalive_projection pid r (Receipts.initialized_keepalive trace placeholders pre post pid r position)

end Leanux.Proofs.WG.TransmitSecurity.Staged
