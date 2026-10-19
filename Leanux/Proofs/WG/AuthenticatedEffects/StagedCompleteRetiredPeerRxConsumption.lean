import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxAdmissionFrames

/-! One original consumeData admission determines the exact carrier and its
final queue/disposal choice. The receipt retains the same source cut used by
the existing receive observer, without selecting an endpoint ledger afresh. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits DurableHolders

def ExactConsumption (holders : DurableHolders) (carriers : RxCredits.Ledger)
    (loans : Reservations) (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (w v : WGWorld) (a b : Ambient) (r : WGRunWitness (Option RxOrigin.Admission)) : Prop :=
  r.before = w ∧ r.ambientBefore = a ∧ r.Valid (RxOrigin.admitSource msg src ds) ∧
  match r.value with
  | none => r.after = v ∧ r.ambientAfter = b ∧ Account holders carriers loans v
  | some ctx => ∃ owner : Owner,
      let c : RxCredits.Carrier := ⟨⟨owner.epoch,ctx.slot⟩,owner,.unpublished⟩
      Phased holders (c :: carriers) loans r.after ∧ StableRx carriers r.after ∧
      owner.slot = ctx.packet.peer ∧ KeyWord ctx.packet.keypair ctx.packet.peer r.after ∧
      RxOrigin.Admitted msg src ds ctx w r.after a r.ambientAfter ∧
      ∃ ret middle aa,
        ((enqueuePerDeviceAndPeerRx ctx.slot).run r.after).run r.ambientAfter = .ok ((ret,middle),aa) ∧
        ((finishAfter ctx ret).run middle).run aa = .ok (((),v),b) ∧
        (ret = 0 ∨ ret = -ENOSPC ∨ ret = -EPIPE) ∧
        (if ret = -ENOSPC then Account holders carriers loans v ∧ packetAt v c.packet = none
         else Account holders (enqueued c :: carriers) loans v)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
