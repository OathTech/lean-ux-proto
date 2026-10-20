import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedHandshakeCanonical

/-! Handshake bookkeeping and passive receipts preserve the packet account.
Consumer atoms use their counted native contracts, and keepalive/release
remain explicit callbacks rather than quiet updates. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev Carrier := WorkService.Points.Carrier
abbrev Checked (action : PrefixM Event α) := WorkService.Points.Checked action

theorem Native.checked (token : Native) : Checked token.action := by
  cases token with
  | quiet body frame=>
    exact Consume.Leaf.native_checked body frame
  | metadata body source=>
    exact Consume.Leaf.native_checked body source.frame
  | captured body frame=>
    exact CompletePoll.state _
      (StatePrefixPreserves.captureWGObserved (CompletePassive.native _ CompleteProduct.account_safe body frame))
  | session pid=>
    exact CompletePoll.state _ (CompleteHandshake.session _ CompleteProduct.account_safe pid)
  | initiation mac=>
    exact CompletePoll.state _ (CompleteHandshake.initiation _ CompleteProduct.account_safe mac)
  | response mac=>
    exact CompletePoll.state _ (CompleteHandshake.response _ CompleteProduct.account_safe mac)
  | cookieConsumed bytes=>
    exact CompletePoll.state _ (CompleteHandshake.cookie_consumed _ CompleteProduct.account_safe bytes)
  | protocol pid bytes=>
    exact CompletePoll.state _ (CompleteHandshake.protocol _ CompleteProduct.account_safe pid bytes)
  | cookie mac bytes src=>
    exact CompletePoll.state _ (CompleteHandshake.cookie _ CompleteProduct.account_safe mac bytes src)
  | scope event=>
    exact CompletePoll.state _
      (CompletePassive.emit _ CompleteProduct.account_safe (.scope event) rfl (fun _=>rfl))
  | note kind pid=>
    exact CompletePoll.state _
      (CompletePassive.emit _ CompleteProduct.account_safe (.old (.handshake (.callback kind pid))) rfl (fun _=>rfl))
  | exchange event=>
    exact CompletePoll.state _
      (CompletePassive.emit _ CompleteProduct.account_safe (.exchange event) rfl (fun _=>rfl))

theorem Child.checked (token : Child) : Checked token.action := by
  cases token with
  | keepalive pid=>
    exact CompletePoll.state _ (CompleteProduct.source_state (CompleteTransmit.keepalive pid))
  | release peer=>
    exact CompletePoll.state _ (CompleteSource.original peer _ CompleteProduct.account_safe)

theorem Shape.checked (shape : Shape action) : Checked action := by
  induction shape with
  | pure value=>
    exact CompletePoll.pure_checked _ CompleteProduct.account_safe value
  | native token=>
    exact token.checked
  | leaf source=>
    exact source.checked
  | child token=>
    exact token.checked
  | bind head tail ihHead ihTail=>
    exact CompletePoll.bind_checked _ ihHead ihTail

theorem Shape.normal (shape : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h=(.ok (value,u),middle)) : Carrier middle u := by
  obtain ⟨_,_,_,kept⟩:=shape.checked w h before
  rw [performed] at kept
  exact kept

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
