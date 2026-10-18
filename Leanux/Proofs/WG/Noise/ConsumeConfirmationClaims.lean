import Leanux.Proofs.WG.Noise.ConsumeConfirmationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConsumeConfirmation
open Std.Do
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues MaterialOrigin

theorem observation_valid_facts (observation : ConfirmationObservation)
    (valid : observation.Valid) : observation.Facts := by
  obtain ⟨r,c,rfl,rv,endpoint,confirm,tail⟩ := valid
  obtain ⟨other,ep',co',tail',facts⟩ := receipt_observation r rv
  have eq1 : c.before = other.before ∧ c.ambientBefore = other.ambientBefore := by
    rw [endpoint] at ep'
    exact (Prod.mk.inj (Except.ok.inj ep')).imp (fun h => (Prod.mk.inj h).2) _root_.id
  have eq2 : c.value = other.value ∧ c.after = other.after ∧ c.ambientAfter = other.ambientAfter := by
    change ((receivedWithKeypair r.peer r.packet.keypair).run c.before).run c.ambientBefore =
      .ok ((c.value,c.after),c.ambientAfter) at confirm
    change ((receivedWithKeypair r.peer r.packet.keypair).run other.before).run other.ambientBefore =
      .ok ((other.value,other.after),other.ambientAfter) at co'
    rw [← eq1.1,← eq1.2,confirm] at co'
    exact ⟨(Prod.mk.inj (Prod.mk.inj (Except.ok.inj co')).1).1,
      (Prod.mk.inj (Prod.mk.inj (Except.ok.inj co')).1).2,
      (Prod.mk.inj (Except.ok.inj co')).2⟩
  cases c
  cases other
  simp only at eq1 eq2
  rcases eq1 with ⟨rfl,rfl⟩
  rcases eq2 with ⟨rfl,rfl,rfl⟩
  exact facts

/-- Actual initialized event linkage. It applies also to committed consume
receipts before a later Stop, but says nothing about an uncommitted inner call. -/
theorem initialized_receipt_observation (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence id : Nat) (stamp : Lifetimes.PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp r :: post) :
    ∃ observation : ConfirmationObservation, observation.Valid ∧ observation.Facts ∧
      observation.peer = r.peer ∧ observation.packet = r.packet ∧
      observation.entry = Campaign2.snapshot r.run.before r.run.ambientBefore ∧
      observation.finish = Campaign2.snapshot r.run.after r.run.ambientAfter := by
  obtain ⟨a,b,decrypt,out,pid,published,ambient,history,publication,certified⟩ :=
    PublicationRunner.consumed trace placeholders pre post occurrence id stamp r position
  have rv := certified.1.1
  obtain ⟨c,endpoint,confirm,tail,facts⟩ := receipt_observation r rv
  exact ⟨projects r c,⟨r,c,rfl,rv,endpoint,confirm,tail⟩,facts,rfl,rfl,rfl,rfl⟩


theorem confirmed_stamp_effect (r : ConfirmationObservation) (valid : r.Valid)
    (stamp : Nat) (confirmed : r.ConfirmedStamp stamp) :
    ∃ (d before final : Device) (p read after : Peer) (key entryKey : Keypair),
      r.entry.wg.device = some d ∧ d.peers[r.peer]? = some p ∧
      d.keypairs[r.packet.keypair]? = some entryKey ∧ entryKey.internalId = stamp ∧
      p.keypairNext = some r.packet.keypair ∧
      r.before.wg.device = some before ∧ before.peers[r.peer]? = some read ∧
      before.keypairs[r.packet.keypair]? = some key ∧ key.internalId = stamp ∧
      r.after.wg.device = some final ∧ final.peers[r.peer]? = some after ∧
      after.keypairCurrent = some r.packet.keypair ∧ after.keypairNext = none := by
  obtain ⟨d,p,before,read,final,hd,hp,hb,hr,slots,stamps,hf,effect,matched⟩ :=
    observation_valid_facts r valid
  have keyEntry : (d.keypairs[r.packet.keypair]?).map Keypair.internalId = some stamp := by
    simpa only [projectedStampAt,hd,Option.bind_some] using confirmed.2
  obtain ⟨entryKey,he,heStamp⟩ := Option.map_eq_some_iff.mp keyEntry
  have keyBefore : (before.keypairs[r.packet.keypair]?).map Keypair.internalId = some stamp := by
    simpa only [projectedStampAt,hb,Option.bind_some] using stamps.trans confirmed.2
  obtain ⟨key,hk,hkStamp⟩ := Option.map_eq_some_iff.mp keyBefore
  have effectTrue : ConfirmationEffect r.peer r.packet.keypair before read true final := by
    simpa only [confirmed.1] using effect
  have peer := confirmationEffect_peer r.peer r.packet.keypair before final read true hr effectTrue
  exact ⟨d,before,final,p,read,rotationPeer (confirmationPlan read r.packet.keypair) read,
    key,entryKey,hd,hp,he,heStamp,matched.mp confirmed.1,hb,hr,hk,hkStamp,hf,peer,rfl,rfl⟩


end Leanux.Proofs.WG.Noise.ConsumeConfirmation
