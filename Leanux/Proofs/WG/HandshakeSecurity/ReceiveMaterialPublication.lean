import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialFrames

/-! Successful native publication retains the exact allocation core read by
AEAD. Only the separate numeric frontier bound is assumed at this local cut;
whole-run transport must derive it from initialized C1 allocation facts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity AuthenticatedEffects Responder

/-- Successful decrypt and the actual publication suffix do not change any
resident key core or the numeric key-slot frontier. -/
theorem published_core (id : SkbId) (r : WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (v : WGWorld) (ambient : Ambient)
    (published : Published id r out pid v ambient) :
    pool v = pool r.before ∧ ResidentMaterial.cursor v = ResidentMaterial.cursor r.before := by
  obtain ⟨run,output,checked,checkedAmbient,installed,installedAmbient,hbranch,hstore,hpub⟩ := published
  obtain ⟨d,k,hd,hp,hk,valid,decrypt,record,aead⟩ := RxOrigin.decrypt_receipt id r out run output
  have ka := decrypt_kernel _ _ _ _ _ _ decrypt
  have kb : checked = r.after := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .decWorkerDecrypted true) (fun g => g = r.after))
    r.after r.ambientAfter true checked checkedAmbient rfl hbranch
  have hchecked : checked.dev = some d := by simp [kb,ka,hd]
  rw [Packets.setRxSkb_run checked checkedAmbient d id r.value.1 (fun _ => out) hchecked hp] at hstore
  cases hstore
  obtain ⟨pubdev,pkt,key,p,hdev,hpkt,hkey,word,hpeer,effect⟩ := publish_execution _ _ _ _ _ _ _ hpub
  have ed : pubdev = {d with rxSkbs := d.rxSkbs.insert id out} := Option.some.inj
    (hdev.symm.trans (by simp [Packets.update,hchecked]))
  subst pubdev
  have hfinal := congrArg WGStoreView.dev effect
  change v.dev = some _ at hfinal
  constructor
  · funext slot
    simp only [pool,hfinal,hd,Option.bind_some]
  · simp only [ResidentMaterial.cursor,hfinal,hd,Option.map_some]

/-- The actual publication constructs one certificate with its decrypt key's
allocation stamp. Successful later resident-key reads may use this conditional
binding; no key survival is presumed. -/
theorem publication_certificate (id : SkbId) (r : WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (v : WGWorld) (ambient : Ambient)
    (published : Published id r out pid v ambient) (pre post : List TransportDriver.OriginEvent) :
    ∃ core, Certificate (pre ++ .receipt (.decrypt id r) :: post) id {out with state := .crypted} v core ∧
      ∀ current, pool v out.keypair = some current → current = core := by
  obtain ⟨d,k,hd,hp,hk,valid,decrypt,record,aead⟩ := RxOrigin.decrypt_receipt id r out published.1 published.2.1
  have slot : out.keypair = r.value.1.keypair := by
    have projected := congrArg RxPacket.keypair record
    exact projected
  have old : pool r.before out.keypair = some (keyCore k) := by simp only [pool,hd,Option.bind_some,slot,hk,Option.map_some]
  refine ⟨keyCore k,?_,?_⟩
  · exact ⟨pre,post,r,out,pid,v,ambient,rfl,published,rfl,
      (TransportPublication.published_packet id r out pid v ambient published).2,old⟩
  · intro current resident
    rw [(published_core id r out pid v ambient published).1,old] at resident
    exact Option.some.inj resident.symm

theorem publication_below (id : SkbId) (r : WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (v : WGWorld) (ambient : Ambient)
    (published : Published id r out pid v ambient)
    (bound : ∀ d, r.before.dev = some d → r.value.1.keypair < d.nextKeypairId)
    (d : Device) (device : v.dev = some d) : out.keypair < d.nextKeypairId := by
  obtain ⟨prior,k,hd,hp,hk,valid,decrypt,record,aead⟩ := RxOrigin.decrypt_receipt id r out published.1 published.2.1
  have same := (published_core id r out pid v ambient published).2
  have frontier : d.nextKeypairId = prior.nextKeypairId := by
    simpa only [ResidentMaterial.cursor,hd,device,Option.map_some,Option.some.injEq] using same
  have slot : out.keypair = r.value.1.keypair := by
    have projected := congrArg RxPacket.keypair record
    exact projected
  rw [frontier,slot]
  exact bound prior hd

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
