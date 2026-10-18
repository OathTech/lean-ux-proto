import Leanux.Proofs.WG.Index.SenderIndexFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise TimerDiscipline Std.Do Leanux.Proofs.Framing
open Queues.RxCredits

theorem sendInitiation_preserves_source (pid : PeerId) (P : WGWorld → Prop)
    (last : ∀ now, Ensures (modifyPeer pid fun p => {p with lastSentHandshake := now}) P (fun _ => P))
    (creator : Ensures (createInitiation pid) P (fun _ => P))
    (mac : ∀ msg, Ensures (addMacToPacket pid msg) P (fun _ => P))
    (traversal : Ensures (timersTraversal pid) P (fun _ => P))
    (sent : Ensures (timersAnyAuthenticatedPacketSent pid) P (fun _ => P))
    (send : ∀ msg, Ensures (sendBufferToPeer pid msg) P (fun _ => P))
    (initiated : Ensures (timersHandshakeInitiated pid) P (fun _ => P)) :
    Ensures (sendHandshakeInitiation pid) P (fun _ => P) := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a r out b pre run; cases run; exact pre
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g a r out b pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g a r out b pre run).1
  have hclock (site : HiddenSite) : Ensures (hiddenClock64 site : WG.M Int64) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hiddenClock64 site) P)
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hlimited (value : Int64) : Ensures (branchExpired .initRateLimited value REKEY_TIMEOUT (!·)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr ((Leanux.Proofs.Framing.branchExpired_sameWGWorld _ _ _ _).wp P)
  have hstop {α : Type} (what : String) : Ensures (invariant what : WG.M α) P (fun _ => P) := by
    intro g a r out b pre run
    simp [invariant,AmbientM.invariant] at run
    cases run
  have prelude : Ensures (initiationTraversalPrelude pid) P (fun _ => P) := by
    unfold initiationTraversalPrelude
    refine ensures_bind _ _ hread ?_
    intro p
    refine ensures_bind _ _ (hlimited p.lastSentHandshake) ?_
    intro limited
    cases limited with
    | true => exact hpure none
    | false =>
      refine ensures_bind _ _ (hclock _) ?_
      intro now
      rw [← bind_assoc]
      refine ensures_bind _ _ (last now) ?_
      intro _
      refine ensures_bind _ _ creator ?_
      intro created
      refine ensures_bind _ _ (hbranch _ _) ?_
      intro made
      cases made with
      | false => exact hpure none
      | true =>
        cases created with
        | none => exact hstop _
        | some msg => exact ensures_bind _ _ (mac msg) (fun value => hpure (some value))
  have finish (msg : List UInt8) : Ensures (initiationTraversalFinish pid msg) P (fun _ => P) := by
    unfold initiationTraversalFinish
    refine ensures_bind _ _ sent ?_
    intro _
    refine ensures_bind _ _ (hclock _) ?_
    intro now
    rw [← bind_assoc]
    refine ensures_bind _ _ (last now) ?_
    intro _
    exact ensures_bind _ _ (send msg) (fun _ => initiated)
  rw [← initiationTraversal_source]
  refine ensures_bind _ _ prelude ?_
  intro message
  cases message with
  | none => exact hpure ()
  | some msg => exact ensures_bind _ _ traversal (fun _ => finish msg)


theorem senderFrame_device_predicate {α : Type} (action : WG.M α)
    (frame : SameView senderFields action) (D : Device → Prop)
    (stable : ∀ d e, senderDeviceCell e=senderDeviceCell d → D d → D e) :
    Ensures action (fun g => ∀ d,g.dev=some d → D d)
      (fun _ g => ∀ d,g.dev=some d → D d) := by
  intro g a value out b pre run e ending
  have same := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp frame g a value out b run
  cases device : g.dev with
  | none => simp [senderFields,device,ending] at same
  | some d =>
    have cells : senderDeviceCell e=senderDeviceCell d := by
      simpa [senderFields,device,ending] using same
    exact stable d e cells (pre d device)

theorem sendInitiation_device_predicate (pid : PeerId) (D : Device → Prop)
    (stable : ∀ d e, senderDeviceCell e=senderDeviceCell d → D d → D e)
    (creator : Ensures (createInitiation pid) (fun g => ∀ d,g.dev=some d → D d)
      (fun _ g => ∀ d,g.dev=some d → D d)) :
    Ensures (sendHandshakeInitiation pid) (fun g => ∀ d,g.dev=some d → D d)
      (fun _ g => ∀ d,g.dev=some d → D d) := by
  apply sendInitiation_preserves_source pid _ ?_ creator ?_ ?_ ?_ ?_ ?_
  · intro now
    exact senderFrame_device_predicate _ (sender_modifyPeer pid (fun p => {p with lastSentHandshake := now}) (fun _ => rfl)) D stable
  · intro msg
    exact senderFrame_device_predicate _ (sender_mac pid msg) D stable
  · exact senderFrame_device_predicate _ (sender_traversal pid) D stable
  · exact senderFrame_device_predicate _ (sender_delTimer pid .sendKeepalive) D stable
  · intro msg
    exact senderFrame_device_predicate _ (sender_fields_socket pid msg) D stable
  · exact senderFrame_device_predicate _ (fun initial =>
      (ensures_iff _ _ _).mp (sender_initiated_frame pid initial)) D stable

end Leanux.Proofs.WG.Index
