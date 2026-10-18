import Leanux.Proofs.WG.Noise.ConsumeConfirmationModel
import Leanux.Proofs.WG.Noise.CounterStampFrames
import Leanux.Proofs.WG.Packets.PublicationRunner
import Leanux.Proofs.WG.Queues.CurrentSlotCompletion
import Leanux.Proofs.WG.Noise.ConfirmationSequenceEffects
import Leanux.Proofs.WG.Noise.RotationSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConsumeConfirmation
open Std.Do
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues MaterialOrigin

def afterConfirmation (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    WG.M (Option (List UInt8)) := do
  if ← branch .doneReceivedNew confirmed then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid
  let ready ← RxCredits.prepareRest pid pkt
  match ready with
  | none => pure none
  | some ready => Packets.rxFinish pid ready

theorem source (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    consumeDataDone pid pkt ep = (do
      setPeerEndpoint pid ep
      let confirmed ← receivedWithKeypair pid pkt.keypair
      afterConfirmation pid pkt confirmed) := by
  rw [Packets.consumeDataDone_factor, RxCredits.rxPrepare_factor]
  simp only [RxCredits.promoteAndSend,afterConfirmation,bind_assoc,RxCredits.bind_if_source,pure_bind]
  rfl

theorem receipt_cut (r : RxDisposition.ConsumeReceipt) (valid : r.Valid) :
    ∃ (d : Device) (p : Peer) (c : WGRunWitness Bool)
      (before : Device) (read : Peer) (final : Device),
      r.run.before.dev = some d ∧ d.peers[r.peer]? = some p ∧
      ((setPeerEndpoint r.peer r.endpoint).run r.run.before).run r.run.ambientBefore =
        .ok (((),c.before),c.ambientBefore) ∧
      c.Valid (receivedWithKeypair r.peer r.packet.keypair) ∧
      ((afterConfirmation r.peer r.packet c.value).run c.after).run c.ambientAfter =
        .ok ((r.run.value,r.run.after),r.run.ambientAfter) ∧
      c.before.dev = some before ∧ before.peers[r.peer]? = some read ∧
      CurrentSlots.slotCell read = CurrentSlots.slotCell p ∧
      c.after.dev = some final ∧
      ConfirmationEffect r.peer r.packet.keypair before read c.value final ∧
      (c.value = true ↔ p.keypairNext = some r.packet.keypair) := by
  have whole := valid
  obtain ⟨d,p,hd,hp⟩ := PublicationIdentity.consume_peer_resident r.peer r.packet r.endpoint
    r.run.before r.run.after r.run.ambientBefore r.run.ambientAfter r.run.value whole
  change ((consumeDataDone r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore =
    .ok ((r.run.value,r.run.after),r.run.ambientAfter) at whole
  rw [source,bind_ok_ambient] at whole
  obtain ⟨u,middle,a,endpoint,rest⟩ := whole
  cases u
  rw [bind_ok_ambient] at rest
  obtain ⟨confirmed,next,b,confirm,tail⟩ := rest
  have fields := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) r.peer r.endpoint)
    r.run.before r.run.ambientBefore () middle a endpoint
  have cells := congrFun (congrArg (fun x => x.2.1) fields) r.peer
  cases hm : middle.dev with
  | none => simp [CurrentSlots.fields,hm,hd,hp] at cells
  | some before =>
    cases hr : before.peers[r.peer]? with
    | none => simp [CurrentSlots.fields,hm,hd,hp,hr] at cells
    | some read =>
      have slotEq : CurrentSlots.slotCell read = CurrentSlots.slotCell p := by
        simpa only [CurrentSlots.fields,hm,hd,Option.bind_some,hr,hp,Option.map_some,
          Option.some.injEq] using cells
      obtain ⟨final,hf,effect⟩ := receivedWithKeypair_effect r.peer r.packet.keypair
        before read hr middle a confirmed next b hm confirm
      refine ⟨d,p,⟨confirmed,middle,next,a,b⟩,before,read,final,hd,hp,endpoint,
        confirm,tail,hm,hr,slotEq,hf,effect,?_⟩
      have nextEq : read.keypairNext = p.keypairNext := congrArg (fun x => x.2.2) slotEq
      by_cases matchNext : read.keypairNext = some r.packet.keypair
      · have yes : confirmed = true := (show confirmed = true ∧ _ from
          by simpa only [ConfirmationEffect,matchNext,ite_true] using effect).1
        simp only [yes,true_iff]
        exact nextEq ▸ matchNext
      · have no : confirmed = false := (show confirmed = false ∧ _ from
          by simpa only [ConfirmationEffect,matchNext,ite_false] using effect).1
        simp only [no,Bool.false_eq_true,false_iff]
        exact fun found => matchNext (nextEq.trans found)


def projects (r : RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool) :
    ConfirmationObservation :=
  ⟨r.peer,r.packet,r.endpoint,
    Campaign2.snapshot r.run.before r.run.ambientBefore,
    Campaign2.snapshot c.before c.ambientBefore,
    Campaign2.snapshot c.after c.ambientAfter,
    Campaign2.snapshot r.run.after r.run.ambientAfter,c.value,r.run.value⟩

theorem receipt_observation (r : RxDisposition.ConsumeReceipt) (valid : r.Valid) :
    ∃ c : WGRunWitness Bool,
      ((setPeerEndpoint r.peer r.endpoint).run r.run.before).run r.run.ambientBefore =
        .ok (((),c.before),c.ambientBefore) ∧
      c.Valid (receivedWithKeypair r.peer r.packet.keypair) ∧
      ((afterConfirmation r.peer r.packet c.value).run c.after).run c.ambientAfter =
        .ok ((r.run.value,r.run.after),r.run.ambientAfter) ∧
      (projects r c).Facts := by
  obtain ⟨d,p,c,before,read,final,hd,hp,endpoint,confirm,tail,hbefore,hread,slots,hfinal,effect,iffNext⟩ :=
    receipt_cut r valid
  have stamped := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (endpoint_stamp r.peer r.endpoint r.packet.keypair)
      r.run.before r.run.ambientBefore () c.before c.ambientBefore endpoint
  exact ⟨c,endpoint,confirm,tail,d,p,before,read,final,hd,hp,hbefore,hread,slots,
    stamped,hfinal,effect,iffNext⟩


/-- The source witness ties all three native calls to one original consume. -/
def ConfirmationObservation.Valid (observation : ConfirmationObservation) : Prop :=
  ∃ (r : RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool),
    projects r c = observation ∧ r.Valid ∧
    ((setPeerEndpoint r.peer r.endpoint).run r.run.before).run r.run.ambientBefore =
      .ok (((),c.before),c.ambientBefore) ∧
    c.Valid (receivedWithKeypair r.peer r.packet.keypair) ∧
    ((afterConfirmation r.peer r.packet c.value).run c.after).run c.ambientAfter =
      .ok ((r.run.value,r.run.after),r.run.ambientAfter)


end Leanux.Proofs.WG.Noise.ConsumeConfirmation
