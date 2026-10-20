import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficConcreteCanonical

/-! Frames for the fixed traffic native tokens and normal callback returns.
All source control flow stays in the canonical module. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal Driver

theorem NativeKind.checked (kind : NativeKind) : CompleteProduct.Checked kind.action := by
  cases kind with
  | base source=>exact source.checked
  | route body=>exact CompleteProduct.routing body
  | pending pid what=>exact CompleteProduct.product_store _ (liftWG_sameProductStore _ (SameView.pure _ _))
  | fixture=>exact CompleteProduct.ambient _
  | sender family dest tos ll=>exact CompleteProduct.product_store _ (senderSource_sameKernel family dest tos ll)
  | packets family addr payload opts=>exact CompleteProduct.product_store _ (xmitPackets_sameKernel family addr payload opts)
  | multicast family addr=>exact CompleteProduct.multicast family addr
  | drained what flags=>exact CompleteProduct.drain what flags
  | receive msg src=>exact CompleteProduct.Execution.received msg src

theorem fixture_checked (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    CompleteProduct.Checked (fixtureTransmit family addr packets mtu) :=
  CompleteProduct.state (CompleteProduct.fixture _ _ (CompleteProduct.transmit family addr packets mtu))

theorem Shape.checked (source : Shape action) : CompleteProduct.Checked action := by
  induction source with
  | pure value=>exact CompleteProduct.pure_checked value
  | native kind=>exact kind.checked
  | stored source=>exact source.checked
  | service source=>exact source.checked
  | poll=>exact CompleteProduct.inline_poll
  | transmit family addr packets mtu=>exact fixture_checked family addr packets mtu
  | bind head tail ihHead ihTail=>exact CompleteProduct.bind_checked ihHead ihTail

theorem Shape.normal (source : Shape action) (before : CompleteProduct.Carrier h w)
    (performed : runPrefix action w h=(.ok (value,u),middle)) : CompleteProduct.Carrier middle u :=
  Xmit.normal source.checked before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
