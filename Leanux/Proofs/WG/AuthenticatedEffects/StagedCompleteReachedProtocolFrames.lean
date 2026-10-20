import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeSocketFrames

/-! Protocol socket receipts introduce no TX birth or terminal demand. Native source frames and the original complete account supply each following bind. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolPoints
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem socket_native_checked (args : ProtocolSocket.Args) (context : CausalEffects.Context Cause) :
    CompletePassive.Checked [] [] CompleteProduct.Safe (ProtocolSocket.socket Event.protocolSocket context args) :=
  CompletePassive.receipt CompleteProduct.Safe CompleteProduct.account_safe
    (liftWGPrefix args.action) (fun run=>Event.protocolSocket ⟨context,args,run⟩)
    (CompletePassive.native CompleteProduct.Safe CompleteProduct.account_safe args.action (NativeSocket.action_frame args))
    (fun _=>rfl) (fun _ _=>rfl)

theorem socket_checked (args : ProtocolSocket.Args) : Checked (socket args) := by
  intro w h before
  rw [socket_at]
  exact CompletePoll.state CompleteProduct.Safe (socket_native_checked args (CausalScope.current scope? h)) w h before

theorem Shape.checked (source : Shape action) : Checked action := by
  induction source with
  | pure value=>exact CompletePoll.pure_checked _ CompleteProduct.account_safe value
  | native body source=>exact Consume.Leaf.native_checked body source.frame
  | socket args=>exact socket_checked args
  | bind head tail ihHead ihTail=>exact CompletePoll.bind_checked _ ihHead ihTail

theorem Shape.normal (source : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h=(.ok (value,u),middle)) : Carrier middle u := by
  obtain ⟨_,_,_,kept⟩:=source.checked w h before
  rw [performed] at kept
  exact kept

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolPoints
