import Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutsideInitiation
import Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutsideResponse
import Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutsideCookie
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceCookieInitialized
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceInitiationRefusal
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceResponseKeys

/-! Complete initialized refusal frames. Only the representation of the two
balanced maps is abstracted: their complete pointwise values and every other WG
field remain observable. A later outer Stop does not erase these actual cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutside
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity

def full (w : WGWorld) := (view w,ResponseLoan.residents w,ResponseLoan.residentKeys w)

theorem final_initiation (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (msg : Key) (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .exchange (.consumeInitiation msg r) :: post) (refused : r.value = none) :
    full r.after = full r.before := by
  have valid := (PeerReference.final_entry trace placeholders pre post (.consumeInitiation msg r) position).2
  have native : ((consumeInitiation msg).run r.before).run r.ambientBefore =
      .ok ((none,r.after),r.ambientAfter) := by
    simpa only [Exchange.Event.Valid,WGRunWitness.Valid,refused] using valid
  have records := PeerReference.final_initiation_refusal_records trace placeholders pre post msg r position refused
  exact Prod.ext (initiation msg r.before r.after r.ambientBefore r.ambientAfter native)
    (Prod.ext records.1 records.2)

theorem final_response (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (msg : Key) (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .exchange (.consumeResponse msg r) :: post) (refused : r.value = none) :
    full r.after = full r.before := by
  have valid := (PeerReference.final_response_entry trace placeholders pre post msg r position).2
  have native : ((consumeResponse msg).run r.before).run r.ambientBefore =
      .ok ((none,r.after),r.ambientAfter) := by
    simpa only [WGRunWitness.Valid,refused] using valid
  exact Prod.ext (response msg r.before r.after r.ambientBefore r.ambientAfter native)
    (Prod.ext
      (PeerReference.final_response_refusal trace placeholders pre post msg r position refused)
      (PeerReference.final_response_refusal_keys trace placeholders pre post msg r position refused))

theorem final_cookie (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (receipt : CookieConsumption.Receipt)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .cookieConsumed receipt :: post)
    (refused : (runWGPrefix (acceptedCookie receipt.input)
      receipt.run.before receipt.run.ambientBefore []).2 = []) :
    full receipt.run.after = full receipt.run.before := by
  have valid := (PeerReference.final_cookie_entry trace placeholders pre post receipt position).2
  exact Prod.ext (cookie receipt.input receipt.run.before receipt.run.after
      receipt.run.ambientBefore receipt.run.ambientAfter refused valid)
    (Prod.ext
      (PeerReference.final_cookie_refusal trace placeholders pre post receipt position refused)
      (PeerReference.final_cookie_refusal_keys trace placeholders pre post receipt position refused))

end Leanux.Proofs.WG.AuthenticatedEffects.RefusalOutside
