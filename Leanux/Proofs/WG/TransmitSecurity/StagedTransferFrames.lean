import Leanux.Proofs.WG.TransmitSecurity.StagedNativeFrames
import Leanux.Proofs.WG.HandshakeSecurity.NonceRejectionFrames
import Leanux.Proofs.WG.Packets.TxFront

/-! Exact native queue splice and purge effects. Their ordered lists preserve
packet positions, including duplicate plaintexts. Counts belong to the source
arms which actually charge them. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def dropped (w : WGWorld) : Option Nat := w.dev.map (·.txDropped)

theorem splice (pid : PeerId) (packets : List Packet) (r : WGRunWitness Unit)
    (valid : r.Valid (xmitSplice pid packets)) :
    ∃ d peer, r.before.dev = some d ∧ d.peers[pid]? = some peer ∧
      r.after.dev = some {d with peers := d.peers.insert pid {peer with staged := peer.staged ++ packets}} ∧
      dropped r.after = dropped r.before := by
  unfold WGRunWitness.Valid xmitSplice at valid
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
  have endpoint : r.after = {r.before with dev := some {d with peers := d.peers.insert pid {first with staged := first.staged ++ packets}}} := by
    simpa only [setPeer,modifyDev,device,Option.map_some] using
      (congrArg (fun out => out.1.2) (Except.ok.inj write)).symm
  exact ⟨d,first,device,resident,by rw [endpoint],by simp only [dropped,endpoint,device,Option.map_some]⟩

theorem splice_projection (pid : PeerId) (packets : List Packet) (r : WGRunWitness Unit)
    (valid : r.Valid (xmitSplice pid packets)) :
    ∃ stamp retained, stagedAt r.after pid = some (stamp,retained ++ packets) := by
  obtain ⟨d,p,_,_,after,_⟩ := splice pid packets r valid
  exact ⟨p.internalId,p.staged,by simp only [stagedAt,after,Option.bind_some,
    Std.TreeMap.getElem?_insert_self,Option.map_some]⟩

/-- The native purge removes precisely the current staged list and charges its
length once. It does not allocate, encrypt or hand any of those packets off. -/
theorem purge (pid : PeerId) (r : WGRunWitness Unit)
    (valid : r.Valid (purgeStagedPackets pid)) :
    ∃ d peer, r.before.dev = some d ∧ d.peers[pid]? = some peer ∧
      r.after.dev = some {d with txDropped := d.txDropped + peer.staged.length, peers := d.peers.insert pid {peer with staged := []}} := by
  unfold WGRunWitness.Valid purgeStagedPackets at valid
  rw [MaterialOrigin.bind_ok_ambient] at valid
  obtain ⟨peer,middle,clock,read,rest⟩ := valid
  obtain ⟨rfl,rfl,d,device,resident⟩ := Origins.getPeer_return pid r.before middle peer r.ambientBefore clock read
  have endpoint : r.after = {r.before with dev := some {d with
      txDropped := d.txDropped + peer.staged.length,
      peers := d.peers.insert pid {peer with staged := []}}} := by
    simpa only [modifyDev,setPeer,StateT.run_bind,StateT.run_modify,StateT.run_pure,
      device,Option.map_some,CounterWindow.except_ok_bind] using
      (congrArg (fun out => out.1.2) (Except.ok.inj rest)).symm
  exact ⟨d,peer,device,resident,by rw [endpoint]⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged
