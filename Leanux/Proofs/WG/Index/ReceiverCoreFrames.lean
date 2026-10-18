import Leanux.Proofs.WG.Index.SenderIndexFrames
import Leanux.Proofs.WG.Noise.CookieReplyTagFrames
import Leanux.Proofs.WG.Origins.SupportCallers
import Leanux.Proofs.WG.Index.ConfigurationIndexFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem reply_sender_fields (src : SkbSource) (msg : List UInt8) :
    SameView senderFields (sendBufferAsReplyToSkb src msg) :=
  sender_fields_of_sendWork_material _ 0 (sendBufferAsReplyToSkb_sendWorkView 0 src msg)
    (Origins.HistorySupport.reply_material src msg)

theorem cookie_fields {α : Type} {action : WG.M α} (same : SameCookie action) :
    SameView ConfigurationIndex.fields action := by
  apply same.of_factor (fun s : WGOwnedView => s.dev.map ConfigurationIndex.deviceFields)
  intro w
  simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,ConfigurationIndex.fields,
    Option.map_map,Function.comp_def]
  rfl


end Leanux.Proofs.WG.Index
