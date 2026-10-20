import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolSendSource

/-! Concrete protocol-send atoms preserve packet accounting. Protocol-socket
events are passive for data tickets; only the explicit peer release can retire
staged tickets. These frames do not claim protocol messages are data packets. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolSend
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev Carrier := WorkService.Points.Carrier
abbrev Checked (action : PrefixM Event α) := WorkService.Points.Checked action

theorem Native.checked (token : Native) : Checked token.action := by
  cases token with
  | work token=>
    exact token.checked
  | before pid=>
    exact Consume.Leaf.native_checked _ (SendWorkerFrames.before_frame pid)
  | create pid=>
    exact Consume.Leaf.native_checked _ (SendWorkerFrames.create pid)
  | jitter site=>
    exact Consume.Leaf.native_checked _
      ((Leanux.Proofs.Framing.jitterBelowRekeyTimeout_sameWGWorld site).factor StagedEntry.view)
  | mac pid bytes=>
    exact Consume.Leaf.native_checked _ (HandshakeFrames.add_mac pid bytes)
  | socket pid bytes=>
    exact CompletePoll.state _
      (CompleteHandshake.protocol CompleteProduct.Safe CompleteProduct.account_safe pid bytes)
  | scope event=>
    exact CompletePoll.state _
      (CompletePassive.emit _ CompleteProduct.account_safe (.scope event) rfl (fun _=>rfl))
  | created pid receipt=>
    exact CompletePoll.state _
      (CompletePassive.emit _ CompleteProduct.account_safe (.exchange (.createInitiation pid receipt)) rfl (fun _=>rfl))

theorem Shape.checked (shape : Shape action) : Checked action := by
  induction shape with
  | pure value=>
    exact CompletePoll.pure_checked _ CompleteProduct.account_safe value
  | native token=>
    exact token.checked
  | leaf source=>
    exact source.checked
  | release peer=>
    exact CompletePoll.state _
      (CompleteSource.original peer CompleteProduct.Safe CompleteProduct.account_safe)
  | bind head tail ihHead ihTail=>
    exact CompletePoll.bind_checked _ ihHead ihTail

theorem Shape.normal (shape : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h=(.ok (value,u),middle)) : Carrier middle u := by
  obtain ⟨suffix,extended,safe,kept⟩:=shape.checked w h before
  rw [performed] at kept
  exact kept

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolSend
