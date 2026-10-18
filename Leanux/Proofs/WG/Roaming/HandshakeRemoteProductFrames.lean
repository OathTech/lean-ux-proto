import Leanux.Proofs.WG.Roaming.HandshakeRemoteFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Framing TimerDiscipline Std.Do

namespace Product

theorem restorePrefix_remotes {α β : Type} (action : WG.M α)
    (restore : Campaign2.Product.Fixture → α → β)
    (frame : SameView destinationAt action) (entry : RemoteMap) :
    Campaign2.Product.Ensures (do
      let fixture := (← Campaign2.Product.read).fixture
      let value ← liftWG action
      pure (restore fixture value))
      (fun s => remoteMap s.toSnapshot = entry)
      (fun _ s => remoteMap s.toSnapshot = entry) := by
  intro w result final pre run
  dsimp only [Campaign2.Product.read,liftWG,StateT.run,StateT.bind,StateT.pure,
    StateT.map,Bind.bind,Pure.pure,Functor.map,Except.bind,Except.pure] at run
  cases native : ((action.run w.wg).run w.ambient) with
  | error stop => simp only [StateT.run] at native; rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value,current⟩,after⟩ := pair
    simp only [StateT.run] at native
    rw [native] at run
    cases run
    exact ((ProjectedAction.iff_run_ambient _ _ _).mp frame
      w.wg w.ambient value current after native).trans pre

theorem lift_remote_effect {α : Type} (action : WG.M α)
    (P : RemoteMap → Prop) (Q : α → RemoteMap → Prop)
    (effect : Ensures action (fun g => P (destinationAt g))
      (fun r g => Q r (destinationAt g))) :
    Campaign2.Product.Ensures (liftWG action)
      (fun s => P (remoteMap s.toSnapshot)) (fun r s => Q r (remoteMap s.toSnapshot)) := by
  intro w result final pre run
  change (((action.run w.wg).run w.ambient) >>= fun ((value,current),after) =>
    .ok (value,{w with wg := current, ambient := after})) = _ at run
  cases native : ((action.run w.wg).run w.ambient) with
  | error stop => rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value,current⟩,after⟩ := pair
    rw [native] at run
    cases run
    exact effect w.wg w.ambient result current after pre native

theorem responseCallPrefix_remotes (msg : List UInt8) (src : SkbSource) (entry : RemoteMap) :
    Campaign2.Product.Ensures (responseCallPrefix msg src)
      (fun s => remoteMap s.toSnapshot = entry)
      (fun _ s => remoteMap s.toSnapshot = entry) :=
  restorePrefix_remotes (Roaming.responseCallPrefix msg src)
    (fun fixture (out : Option Roaming.ResponseCallCut) => out.map (restoreResponseCallCut fixture))
    (Roaming.responseCallPrefix_remotes msg src) entry

theorem initiationCallPrefix_remotes (msg : List UInt8) (src : SkbSource) (entry : RemoteMap) :
    Campaign2.Product.Ensures (initiationCallPrefix msg src)
      (fun s => remoteMap s.toSnapshot = entry)
      (fun _ s => remoteMap s.toSnapshot = entry) :=
  restorePrefix_remotes (Roaming.initiationCallPrefix msg src)
    (fun fixture (out : Option Roaming.InitiationCallCut) => out.map (restoreInitiationCallCut fixture))
    (Roaming.initiationCallPrefix_remotes msg src) entry

theorem responseCallSuffix_remotes (msg : List UInt8) (src : SkbSource)
    (candidate : Option ResponseCallCut) (entry : RemoteMap) :
    Campaign2.Product.Ensures (responseCallSuffix msg src candidate)
      (fun s => remoteMap s.toSnapshot = entry)
      (fun _ s => match candidate with
        | none => remoteMap s.toSnapshot = entry
        | some cut => RemoteRetained (updateRemote entry cut.consumed.input.pid
            (destination (sourceEndpoint src))) (remoteMap s.toSnapshot)) := by
  cases candidate with
  | none => intro w result final pre run; cases run; exact pre
  | some cut =>
    change Campaign2.Product.Ensures (liftWG (do
      setPeerEndpointFromSkb cut.consumed.input.pid src
      Roaming.responseAfterSetter msg cut.consumed.input.pid)) _ _
    refine lift_remote_effect _ (fun map => map = entry)
      (fun _ map => RemoteRetained (updateRemote entry cut.consumed.input.pid
        (destination (sourceEndpoint src))) map) ?_
    refine ensures_bind _ _ (Roaming.setPeerEndpointFromSkb_remotes cut.consumed.input.pid src entry) ?_
    intro _ g a result final after pre run
    exact Roaming.responseAfterSetter_remotes msg cut.consumed.input.pid _ g a result final after
      (.of_eq pre) run

theorem initiationCallSuffix_remotes (msg : List UInt8) (src : SkbSource)
    (candidate : Option InitiationCallCut) (entry : RemoteMap) :
    Campaign2.Product.Ensures (initiationCallSuffix msg src candidate)
      (fun s => remoteMap s.toSnapshot = entry)
      (fun _ s => match candidate with
        | none => remoteMap s.toSnapshot = entry
        | some cut => RemoteRetained (updateRemote entry cut.consumed.pid
            (destination (sourceEndpoint src))) (remoteMap s.toSnapshot)) := by
  cases candidate with
  | none => intro w result final pre run; cases run; exact pre
  | some cut =>
    change Campaign2.Product.Ensures (liftWG (do
      setPeerEndpointFromSkb cut.consumed.pid src
      Roaming.initiationAfterSetter msg cut.consumed.pid)) _ _
    refine lift_remote_effect _ (fun map => map = entry)
      (fun _ map => RemoteRetained (updateRemote entry cut.consumed.pid
        (destination (sourceEndpoint src))) map) ?_
    refine ensures_bind _ _ (Roaming.setPeerEndpointFromSkb_remotes cut.consumed.pid src entry) ?_
    intro _ g a result final after pre run
    exact Roaming.initiationAfterSetter_remotes msg cut.consumed.pid _ g a result final after
      (.of_eq pre) run


end Product

end Leanux.Proofs.WG.Roaming
