import Leanux.Proofs.WG.TimerDiscipline.SendBufferFrame
import Leanux.Proofs.WG.Noise.ResponseTagModel

/-! Tag projection of the campaign-owned socket observation. No second socket
proof layer is introduced: the H6 view retains these fields through its
existing cache, routing, transmission and accounting compositions. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG TimerDiscipline

/-- Variant of the shared send-buffer frame, obtained from the stronger owned
socket view. Every resident peer's optional tag is preserved. -/
theorem sendBufferToPeer_spec_tagMap_variant (pid : PeerId) (msg : List UInt8)
    (entry : Option Device) :
    Ensures (sendBufferToPeer pid msg)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  have same := (ensures_iff _ _ _).mpr
    (sendBufferToPeer_spec_sendWork_variant pid msg
      (sendWorkAt g pid).1 (sendWorkAt g pid).2)
    g ambient result final after rfl run
  have projected := congrArg (fun x : SendWorkView =>
    fun target => x.1.bind fun d => d.2.2 target) same
  have tags : responseTagMap final.dev = responseTagMap g.dev := by
    funext target
    have point := congrFun projected target
    cases initial : g.dev <;> cases ending : final.dev
    all_goals first
      | rfl
      | simpa [responseTagMap, sendWorkAt, sendWorkKernel, sendWorkDevice,
          initial, ending] using point
  exact tags.trans pre

end Leanux.Proofs.WG.Noise
