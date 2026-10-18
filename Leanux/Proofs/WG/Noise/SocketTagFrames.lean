import Leanux.Proofs.WG.TimerDiscipline.SendBufferFrame
import Leanux.Proofs.WG.Noise.ResponseTagModel

/-! Tag projection of the campaign-owned socket observation. No second socket
proof layer is introduced: the H6 view retains these fields through its
existing cache, routing, transmission and accounting compositions. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG TimerDiscipline Std.Do

/-- Forget the queue/frontier fields of any owned socket observation. -/
theorem tagMap_frame_of_sendWork {α : Type} (action : WG.M α) (pid : PeerId)
    (frame : ∀ (q : Option SendWorkDevice) (v : Option SendWorkPeer),
      ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄) (entry : Option Device) :
    Ensures action
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  have same := (ensures_iff _ _ _).mpr
    (frame (sendWorkAt g pid).1 (sendWorkAt g pid).2)
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

/-- Variant of the shared send-buffer frame, obtained from the stronger owned
socket view. Every resident peer's optional tag is preserved. -/
theorem sendBufferToPeer_spec_tagMap_variant (pid : PeerId) (msg : List UInt8)
    (entry : Option Device) :
    Ensures (sendBufferToPeer pid msg)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) :=
  tagMap_frame_of_sendWork _ pid (sendBufferToPeer_spec_sendWork_variant pid msg) entry

end Leanux.Proofs.WG.Noise
