import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayAuthorizedPoll
import Leanux.Proofs.WG.TransmitSecurity.DriverSource

/-! The common driver's real endpoint update precedes confirmation and keeps
the current accepted replay receipt as the final journal entry at that cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {record : TransportDriver.Replay → E}

def ConfirmationInput (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (pid : PeerId) (kid : KeypairId) (h : List E) (w : World) : Prop :=
  ∃ pkt, pkt.peer = pid ∧ pkt.keypair = kid ∧ AtCounter origin replay record pkt true h w

theorem confirmation_input_authenticated
    (input : ConfirmationInput origin replay record pid kid h w) :
    ∃ pre r, h = pre ++ [record r] ∧ r.packet.peer = pid ∧ r.packet.keypair = kid ∧
      r.run.value = true ∧ Certified (pre.filterMap origin) r := by
  obtain ⟨pkt,peer,key,_,pre,r,position,packet,value,certified⟩ := input
  exact ⟨pre,r,position,packet ▸ peer,packet ▸ key,value,certified⟩

theorem shared_consumer_authorized (hooks : TransmitSecurity.Driver.Hooks E)
    (hc : ∀ pid kid, PrefixEnsures (ConfirmationInput origin replay record pid kid)
      (Safe origin replay) (liftWGObserver (hooks.confirmation pid kid)) (fun _ => Inv origin replay))
    (ht : ∀ pid pkt value, Preserves (origin := origin) (replay := replay)
      (liftWGObserver (TransmitSecurity.Driver.receiveTailObserved hooks pid pkt value)))
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) (peer : pkt.peer = pid) :
    PrefixEnsures (AtCounter origin replay record pkt true) (Safe origin replay)
      (liftWGObserver (TransmitSecurity.Driver.consumeObserved hooks pid pkt ep))
      (fun _ => Inv origin replay) := by
  unfold TransmitSecurity.Driver.consumeObserved
  simp only [liftWGObserver_bind,liftWGObserver_lift]
  apply PrefixEnsures.bind (atCounter_native (setPeerEndpoint pid ep)
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid ep).factor Prod.snd))
  intro _
  apply PrefixEnsures.bind ((hc pid pkt.keypair).consequence
    (fun _ _ hi => ⟨pkt,peer,rfl,hi⟩) (fun _ _ _ hi => hi))
  exact ht pid pkt

theorem shared_poll_authorized (hooks : TransmitSecurity.Driver.Hooks E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (counter : hooks.counterCheck = TransportDriver.counter record)
    (hc : ∀ pid kid, PrefixEnsures (ConfirmationInput origin replay record pid kid)
      (Safe origin replay) (liftWGObserver (hooks.confirmation pid kid)) (fun _ => Inv origin replay))
    (ht : ∀ pid pkt value, Preserves (origin := origin) (replay := replay)
      (liftWGObserver (TransmitSecurity.Driver.receiveTailObserved hooks pid pkt value)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (hr : ∀ gro bytes, Preserves (origin := origin) (replay := replay)
      (napiGroReceivePrefix toStack gro bytes))
    (hf : ∀ gro, Preserves (origin := origin) (replay := replay)
      (napiGroFlushAllPrefix toStack gro))
    (pid : PeerId) (budget : Nat) :
    Preserves (origin := origin) (replay := replay)
      (TransmitSecurity.Driver.pollObserved hooks pid budget toStack) := by
  unfold TransmitSecurity.Driver.pollObserved
  simp only [liftWGObserver_lift,counter]
  exact poll_authorized origin replay record inverse quiet _ _ _
    (shared_consumer_authorized hooks hc ht) hr hf pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
