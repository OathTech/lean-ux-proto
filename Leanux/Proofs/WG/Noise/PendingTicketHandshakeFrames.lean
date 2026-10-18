import Leanux.Proofs.WG.Noise.PendingSocketFrames
import Leanux.Proofs.WG.Noise.PendingTicketEndpointFrames
import Leanux.Proofs.Framing.WGCookie
import Leanux.Proofs.WG.Queues.SlotRemoval
import Leanux.Proofs.WG.Roaming.EndpointSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing

/-- Cookie-only changes preserve pending slots, allocation stamps and frontier. -/
theorem frame_cookie {α : Type} (action : WG.M α) (frame : SameCookie action) :
    SameView view action := by
  apply frame.of_factor
    (fun v : WGOwnedView => (⟨v.keypairCounter,fun pid => v.dev.bind fun d => pending d pid⟩ : Store PeerId))
    view
  intro w
  apply Store.ext
  · rfl
  · funext pid
    change w.dev.bind (fun d => pending d pid) =
      (w.dev.map cookieDevice).bind (fun d => pending d pid)
    cases w.dev <;> rfl

theorem cookieMessageCreate_frame (index : Nat) (src : SkbSource) (mac : List UInt8) :
    SameView view (cookieMessageCreate index src mac) :=
  frame_cookie _ (cookieMessageCreate_sameCookie index src mac)

theorem cookieValidatePacket_frame (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    SameView view (cookieValidatePacket msg src checkCookie) :=
  frame_cookie _ (cookieValidatePacket_sameCookie msg src checkCookie)

theorem loadPhase_frame : SameView view Cookies.loadPhase :=
  frame_store Cookies.loadPhase_sameStore

theorem addMacToPacket_frame (pid : PeerId) (msg : List UInt8) :
    SameView view (addMacToPacket pid msg) :=
  frame_from_fields (CurrentSlots.Removal.addMac_fields pid msg)
    (Keypairs.WGTransitions.addMacToPacket_sameSnapshot pid msg)

theorem endpointFromSkb_frame (src : SkbSource) : SameView view (endpointFromSkb src) := by
  intro initial
  exact hoare_consequence (Roaming.endpointFromSkb_exact src (fun w => view w = initial))
    (fun _ h => h) (fun _ _ h => h.1)

theorem setPeerEndpointFromSkb_frame (pid : PeerId) (src : SkbSource) :
    SameView view (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  apply SameView.bind (endpointFromSkb_frame src)
  intro endpoint
  apply SameView.bind (frame_ambient (AmbientM.branch .epFromSkbOk endpoint.isSome))
  intro ok
  cases ok with
  | false => exact SameView.pure _ _
  | true =>
    cases endpoint with
    | none => exact frame_ambient (AmbientM.invariant "unreachable")
    | some e => exact setPeerEndpoint_frame pid e

theorem sendHandshakeCookie_frame (msg : List UInt8) (src : SkbSource) :
    SameView view (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookie
  apply SameView.bind (cookieMessageCreate_frame _ _ _)
  intro buffer
  exact sendBufferAsReplyToSkb_frame src buffer

end Leanux.Proofs.WG.Noise.PendingTickets
