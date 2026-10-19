import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialReplayAuthorized
import Leanux.Proofs.WG.TransmitSecurity.DriverSource

/-! Native endpoint update keeps the exact accepted packet and its allocation
certificate available at the shared confirmation callback. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Replay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {record : TransportDriver.Replay → E}

def ConfirmationInput (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (pid : PeerId) (kid : KeypairId) (h : List E) (w : World) : Prop :=
  ∃ pkt, pkt.peer = pid ∧ pkt.keypair = kid ∧ AtCounter origin replay record pkt true h w

/-- The exact incoming accepted packet was authenticated under the allocation
resident at confirmation, given the locally carried RX material invariant. -/
theorem confirmation_input_material
    (input : ConfirmationInput origin replay record pid kid h w)
    (quiet : ∀ r, origin (record r) = none)
    (resident : pool w.wg kid = some core) :
    ∃ pre r, h = pre ++ [record r] ∧ r.packet.peer = pid ∧ r.packet.keypair = kid ∧
      r.run.value = true ∧ Certified (pre.filterMap origin) r ∧
      Certificate (pre.filterMap origin) r.skb r.packet w.wg core := by
  obtain ⟨pkt,peer,key,atCounter⟩ := input
  obtain ⟨pre,r,position,packet,value,certified,material⟩ :=
    atCounter.material quiet (by simpa only [key] using resident)
  exact ⟨pre,r,position,packet ▸ peer,packet ▸ key,value,certified,packet ▸ material⟩

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
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid ep).factor Prod.snd)
    (fun _ => ReceiveMaterial.endpoint pid ep))
  intro _
  apply PrefixEnsures.bind ((hc pid pkt.keypair).consequence
    (fun _ _ hi => ⟨pkt,peer,rfl,hi⟩) (fun _ _ _ hi => hi))
  exact ht pid pkt

theorem shared_poll_authorized (hooks : TransmitSecurity.Driver.Hooks E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (counter : hooks.counterCheck = TransportDriver.counter record)
    (enter : hooks.candidateEnter = fun _ _ => pure 0)
    (leave : hooks.candidateLeave = fun _ => pure ())
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
  simp only [liftWGObserver_lift,counter,enter,leave,CandidatePoll.neutral]
  exact poll_authorized origin replay record inverse quiet _ _ _
    (shared_consumer_authorized hooks hc ht) hr hf pid budget

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Replay
