import Leanux.Proofs.WG.HandshakeSecurity.NonceRejectionSource

/-! The rejection arm's actual write effects, before reference release or any
later hidden-clock failure. The packet list is restored as a whole prefix. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def dropped (w : WGWorld) : Option Nat := w.dev.map (·.txDropped)

theorem invalidation (kid : KeypairId) (r : WGRunWitness Unit) (valid : r.Valid (invalidate kid)) :
    ∃ d key, r.before.dev = some d ∧ d.keypairs[kid]? = some key ∧
      r.after.dev = some {d with keypairs := d.keypairs.insert kid {key with sending := {key.sending with isValid := false}}} ∧
      dropped r.after = dropped r.before := by
  unfold WGRunWitness.Valid invalidate at valid
  rw [MaterialOrigin.bind_ok_ambient] at valid
  obtain ⟨key,middle,clock,read,write⟩ := valid
  obtain ⟨rfl,rfl,d,device,resident⟩ := KeyTimes.getKeypair_return kid r.before middle key
    r.ambientBefore clock read
  have endpoint : r.after = {r.before with dev := some {d with keypairs := d.keypairs.insert kid {key with sending := {key.sending with isValid := false}}}} := by
    simpa only [setKeypair,modifyDev,device,Option.map_some] using
      (congrArg (fun out => out.1.2) (Except.ok.inj write)).symm
  exact ⟨d,key,device,resident,by rw [endpoint],by simp only [dropped,endpoint,device,Option.map_some]⟩

theorem restoration (pid : PeerId) (packets : List Packet) (r : WGRunWitness Unit)
    (valid : r.Valid (restore pid packets)) :
    ∃ d peer, r.before.dev = some d ∧ d.peers[pid]? = some peer ∧
      r.after.dev = some {d with peers := d.peers.insert pid {peer with staged := packets ++ peer.staged}} ∧
      dropped r.after = dropped r.before := by
  unfold WGRunWitness.Valid restore at valid
  rw [MaterialOrigin.bind_ok_ambient] at valid
  obtain ⟨first,middle,clock,read,rest⟩ := valid
  obtain ⟨rfl,rfl,d,device,resident⟩ := Origins.getPeer_return pid r.before middle first r.ambientBefore clock read
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨second,middle,clock,read,write⟩ := rest
  obtain ⟨rfl,rfl,e,device',resident'⟩ := Origins.getPeer_return pid r.before middle second r.ambientBefore clock read
  have sameDevice := Option.some.inj (device.symm.trans device')
  subst e
  have samePeer := Option.some.inj (resident.symm.trans resident')
  subst second
  have endpoint : r.after = {r.before with dev := some {d with peers := d.peers.insert pid {first with staged := packets ++ first.staged}}} := by
    simpa only [setPeer,modifyDev,device,Option.map_some] using
      (congrArg (fun out => out.1.2) (Except.ok.inj write)).symm
  exact ⟨d,first,device,resident,by rw [endpoint],by simp only [dropped,endpoint,device,Option.map_some]⟩

end Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
