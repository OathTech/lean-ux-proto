import Leanux.Proofs.WG.HandshakeSecurity.ResponseRefusalKeys
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceRefusal

/-! Full keypair records on the same initialized refused-response receipt
whose native entry already supplies positive peer references. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem final_response_refusal_keys (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List AuthenticatedEffects.CausalJournal.Event) (msg : Key)
    (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2 =
      pre ++ AuthenticatedEffects.CausalJournal.Event.exchange (.consumeResponse msg r) :: post)
    (refused : r.value = none) :
    AuthenticatedEffects.ResponseLoan.residentKeys r.after =
      AuthenticatedEffects.ResponseLoan.residentKeys r.before := by
  obtain ⟨positive,valid⟩ := final_response_entry trace placeholders pre post msg r position
  apply ResponseKeys.refusal msg r.before r.after r.ambientBefore r.ambientAfter
    (refusal_positive positive)
  simpa only [WGRunWitness.Valid,refused] using valid

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
