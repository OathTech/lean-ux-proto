import Leanux.Proofs.WG.Noise.UncachedSocketTagFrames
import Leanux.Proofs.Framing.WGCookie
import Leanux.Proofs.WG.Roaming.EndpointSource

/-! Cookie creation and reply sending preserve the handshake tag map. The
cookie projection is the landed shared one; the two uncached sockets reuse
the owned tunnel observation. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem tagMap_frame_of_sameCookie {α : Type} (action : WG.M α)
    (frame : Leanux.Proofs.Framing.SameCookie action) (entry : Option Device) :
    Ensures action (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  have tags := frame.of_factor (fun v => responseTagMap v.dev)
    (fun g => responseTagMap g.dev) (by
      intro g
      funext pid
      change responseTagMap g.dev pid = responseTagMap (g.dev.map Framing.cookieDevice) pid
      cases g.dev <;> rfl)
  exact (ensures_iff _ _ _).mpr (tags (responseTagMap entry))

theorem cookieMessageCreate_spec_tagMap_variant (index : Nat) (src : SkbSource)
    (mac : List UInt8) (entry : Option Device) :
    Ensures (cookieMessageCreate index src mac)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) :=
  tagMap_frame_of_sameCookie _
    (Leanux.Proofs.Framing.cookieMessageCreate_sameCookie index src mac) entry

theorem cookieValidatePacket_spec_tagMap_variant (msg : List UInt8) (src : SkbSource)
    (checkCookie : Bool) (entry : Option Device) :
    Ensures (cookieValidatePacket msg src checkCookie)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) :=
  tagMap_frame_of_sameCookie _
    (Leanux.Proofs.Framing.cookieValidatePacket_sameCookie msg src checkCookie) entry

theorem sendBufferAsReplyToSkb_sendWorkView (pid : PeerId) (src : SkbSource)
    (buffer : List UInt8) (q : Option TimerDiscipline.SendWorkDevice)
    (v : Option TimerDiscipline.SendWorkPeer) :
    ⦃fun w => ⌜TimerDiscipline.sendWorkAt w pid = (q, v)⌝⦄ sendBufferAsReplyToSkb src buffer
      ⦃⇓? _ w => ⌜TimerDiscipline.sendWorkAt w pid = (q, v)⌝⦄ := by
  let P : WGWorld → Prop := fun g => TimerDiscipline.sendWorkAt g pid = (q, v)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g a y v b pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    hambient (AmbientM.branch site value)
  have hstop {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) P (fun _ => P) :=
    hambient (AmbientM.invariant message)
  have hendpoint : Ensures (endpointFromSkb src) P (fun _ => P) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr
      (Roaming.endpointFromSkb_exact src P) g ambient result final after pre run).1
  have h4 (e : Endpoint) : Ensures (send4 e none buffer 0 false) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (uncached_sendWorkView pid false e buffer 0 false q v)
  have h6 (e : Endpoint) : Ensures (send6 e none buffer 0 false) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (uncached_sendWorkView pid true e buffer 0 false q v)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes P (fun _ => P)) (hn : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by split <;> assumption
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold sendBufferAsReplyToSkb
  repeat' first
    | exact hpure _
    | exact hbranch _ _
    | exact hstop _
    | exact hambient (AmbientM.hiddenAlloc .replySkb)
    | exact hendpoint
    | exact h4 _
    | exact h6 _
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)
  all_goals cases ‹Option Endpoint›
  all_goals
    repeat' first
      | exact hpure _
      | exact hbranch _ _
      | exact hstop _
      | exact hambient (AmbientM.hiddenAlloc .replySkb)
      | exact h4 _
      | exact h6 _
      | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)

/-- The existing tag interface is a projection of the owned reply-send frame. -/
theorem sendBufferAsReplyToSkb_spec_tagMap_variant (src : SkbSource)
    (buffer : List UInt8) (entry : Option Device) :
    Ensures (sendBufferAsReplyToSkb src buffer)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) :=
  tagMap_frame_of_sendWork _ 0 (sendBufferAsReplyToSkb_sendWorkView 0 src buffer) entry

theorem sendHandshakeCookie_spec_tagMap_variant (msg : List UInt8) (src : SkbSource)
    (entry : Option Device) :
    Ensures (sendHandshakeCookie msg src)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) :=
  ensures_bind _ _ (cookieMessageCreate_spec_tagMap_variant _ _ _ entry)
    (fun buffer => sendBufferAsReplyToSkb_spec_tagMap_variant src buffer entry)

end Leanux.Proofs.WG.Noise
