import Leanux.Proofs.WG.Packets.PublicationIdentity

/-! The actual successful publication retains the resident peer's allocation
stamp and configured static key. Its reference increment and NAPI write are
kept explicit; no liveness, credit, or initialized identity premise is added. -/
namespace Leanux.Proofs.WG.PublicationIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes

theorem published_peer (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (v : WGWorld) (ambient : Ambient) (published : Published id r out pid v ambient) :
    ∃ d k p after,
      r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
      d.keypairs[r.value.1.keypair]? = some k ∧ k.peer = some pid ∧
      d.peers[pid]? = some p ∧ v.dev = some after ∧ after.ifindex = d.ifindex ∧
      after.peers[pid]? = some {p with refcount := p.refcount + 1, napiScheduled := true} := by
  obtain ⟨run, output, checked, checkedAmbient, installed, installedAmbient,
    hbranch, hstore, hpub⟩ := published
  obtain ⟨d, k, hd, hp, hk, _, decrypt, record, _⟩ :=
    RxOrigin.decrypt_receipt id r out run output
  have ka := decrypt_kernel _ _ _ _ _ _ decrypt
  have kb : checked = r.after := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .decWorkerDecrypted true) (fun g => g = r.after))
    r.after r.ambientAfter true checked checkedAmbient rfl hbranch
  have hchecked : checked.dev = some d := by simp [kb, ka, hd]
  rw [Packets.setRxSkb_run checked checkedAmbient d id r.value.1
    (fun _ => out) hchecked hp] at hstore
  cases hstore
  obtain ⟨pubdev, pkt, key, p, hdev, hpkt, hkey, word, hpeer, effect⟩ :=
    publish_execution _ _ _ _ _ _ _ hpub
  have ed : pubdev = {d with rxSkbs := d.rxSkbs.insert id out} :=
    Option.some.inj (hdev.symm.trans (by simp [Packets.update, hchecked]))
  subst pubdev
  have eqpkt : pkt = out := by simpa using hpkt.symm
  subst pkt
  have kid : out.keypair = r.value.1.keypair := by rw [record]
  have ek : key = k := Option.some.inj (hkey.symm.trans (by simpa [kid] using hk))
  subst key
  let after : Device := {d with
    rxSkbs := (d.rxSkbs.insert id out).insert id {out with state := .crypted}
    peers := (d.peers.insert pid {p with refcount := p.refcount + 1}).insert pid
      {p with refcount := p.refcount + 1, napiScheduled := true}}
  have hfinal := congrArg WGStoreView.dev effect
  change v.dev = some _ at hfinal
  refine ⟨d, k, p, after, hd, hp, hk, word, hpeer, ?_, rfl, ?_⟩
  · simpa [after, Packets.update, hchecked] using hfinal
  · simp [after]

end Leanux.Proofs.WG.PublicationIdentity
