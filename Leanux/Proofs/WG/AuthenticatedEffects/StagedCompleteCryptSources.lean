import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCryptNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductNapi
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSourceClosed

/-! Concrete crypt-worker sources preserve paired accounting with native
allocation safety. All poll, encryption, preparation and release leaves are
discharged on their actual observed runs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem poll : Checked hooks.poll :=
  pair_product (CompleteRing.checked Safe account_safe) CryptNative.poll_erases CryptNative.poll

theorem encrypt (item : Option (List SkbId)) : Checked (hooks.encrypt item) :=
  pair_product (CompleteEncrypt.checked Safe account_safe item) (CompleteEncrypt.erases item)
    (native_allocated_product (CryptNative.encrypt_step_erases item) (CryptNative.encrypt_step_allocation item))

theorem prepare : Checked hooks.prepare :=
  pair_product (CompleteDecrypt.checked Safe account_safe) CryptNative.prepare_erases CryptNative.prepare

theorem encrypt_iteration : Checked (Driver.encryptIterObserved hooks) :=
  encrypt_iter poll softirq encrypt

theorem decrypt_iteration : Checked (Driver.decryptIterObserved hooks) :=
  decrypt_iter (decrypt_step prepare (fun pid => state (release (some pid))) softirq irq_exit)

theorem receive_iteration : Checked (Driver.receiveIterObserved hooks) := receive_iter (state handshake)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
