import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsObserved

/-! Append facts and exact native-journal projections for the completion
observer's existing source callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

private theorem send_appends (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) :
    Appends (Completion.send pid skb packet) := by
  unfold Completion.send Completion.socket receiptObserved
  repeat' first
    | with_reducible exact Appends.focus _ _ _
    | (change Appends (focusPrefix _ _ _); exact Appends.focus _ _ _)
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | (change Appends (emitPrefix _); exact fun _ _ => ⟨[_],rfl⟩)
    | with_reducible apply Appends.captureObserved
    | with_reducible apply Appends.bind
    | (with_reducible intro x; try dsimp only)
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem focused_projects (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (inverse : ∀ event, decode (encode event) = some event) :
    Ops.Projects decode (focused encode decode) native where
  step := fun _ => (Appends.lift _).project_focus encode decode inverse
  peer := fun _ => (Appends.focus _ _ _).project_focus encode decode inverse
  modifyPeer := fun _ _ => (Appends.focus _ _ _).project_focus encode decode inverse
  packet := fun _ => (Appends.focus _ _ _).project_focus encode decode inverse
  completion := fun pid item =>
    (show Appends (native.completion pid item) from fun _ _ =>
      ⟨[.disposition (.completion pid item)],rfl⟩).project_focus encode decode inverse
  send := fun pid skb packet => (send_appends pid skb packet).project_focus encode decode inverse
  drop := fun _ _ => (Appends.focus _ _ _).project_focus encode decode inverse
  dispose := fun _ _ _ => (Appends.focus _ _ _).project_focus encode decode inverse
  traversal := fun _ => (Appends.focus _ _ _).project_focus encode decode inverse
  sent := fun _ => (Appends.focus _ _ _).project_focus encode decode inverse
  dataSent := fun _ => (Appends.focus _ _ _).project_focus encode decode inverse
  fresh := fun _ => (Appends.focus _ _ _).project_focus encode decode inverse

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
