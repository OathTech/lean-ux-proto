import Leanux.Proofs.WG.HandshakeSecurity.ResponderCoreProjection
import Leanux.Proofs.WG.AuthenticatedEffects.TransportPublicationFrames

/-! Conditional allocation-stamped RX material. Authentication provenance and
key identity are carried together for each surviving crypted packet. A key may
be removed; a later resident at the packet's old numeric slot must have the
same core. The packet's frontier bound excludes fresh-session installation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity AuthenticatedEffects Responder
variable {id : SkbId} {pkt : RxPacket} {w v : WGWorld} {core : KeyCore}
variable {h later : List TransportDriver.OriginEvent}

def Certificate (h : List TransportDriver.OriginEvent) (id : SkbId) (pkt : RxPacket)
    (w : WGWorld) (core : KeyCore) : Prop :=
  ∃ pre post, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
    h = pre ++ .receipt (.decrypt id r) :: post ∧
    Published id r out pid published ambient ∧ pkt = {out with state := .crypted} ∧
    packetStamp w id = packetStamp r.before id ∧ pool r.before pkt.keypair = some core

def Inv (h : List TransportDriver.OriginEvent) (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → ∀ id pkt, d.rxSkbs[id]? = some pkt → pkt.state = .crypted →
    pkt.keypair < d.nextKeypairId ∧ ∃ core, Certificate h id pkt w core ∧
      ∀ current, pool w pkt.keypair = some current → current = core

theorem Certificate.authenticated (certificate : Certificate h id pkt w core) :
    TransportPublication.Anchor h id pkt w := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,valid,packet,stamp,_⟩ := certificate
  exact ⟨pre,post,r,out,pid,published,ambient,position,valid,packet,stamp⟩

theorem Certificate.append (certificate : Certificate h id pkt w core)
    (suffix : List TransportDriver.OriginEvent) : Certificate (h ++ suffix) id pkt w core := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,valid,packet,stamp,material⟩ := certificate
  exact ⟨pre,post ++ suffix,r,out,pid,published,ambient,
    by simp only [position,List.append_assoc,List.cons_append],valid,packet,stamp,material⟩

theorem Certificate.transport (certificate : Certificate h id pkt w core)
    (stamp : packetStamp v id = packetStamp w id) : Certificate h id pkt v core := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,valid,packet,old,material⟩ := certificate
  exact ⟨pre,post,r,out,pid,published,ambient,position,valid,packet,stamp.trans old,material⟩

theorem Inv.append (before : Inv h w) (suffix : List TransportDriver.OriginEvent) : Inv (h ++ suffix) w := by
  intro d device id pkt resident crypted
  obtain ⟨bound,core,certificate,conditional⟩ := before d device id pkt resident crypted
  exact ⟨bound,core,certificate.append suffix,conditional⟩

theorem Inv.authenticated (before : Inv h w) : TransportPublication.Inv h w := by
  intro id pkt resident crypted
  obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp resident
  exact (before d device id pkt stored crypted).2.choose_spec.1.authenticated

theorem empty (packets : ∀ d, w.dev = some d → d.rxSkbs = {}) : Inv h w := by
  intro d device id pkt resident _
  simp [packets d device] at resident

theorem initial (net bare : Bool) : Inv [] (Runner.initialWG net bare) := by
  apply empty
  intro d device
  cases net <;> cases bare <;> simp [Runner.initialWG] at device <;> subst d <;> rfl

theorem Inv.retains (before : Inv h w)
    (packets : ∀ id pkt, (RxDisposition.nativeRxStore v).2 id = some pkt → pkt.state = .crypted →
      (RxDisposition.nativeRxStore w).2 id = some pkt ∧ packetStamp v id = packetStamp w id)
    (frontier : ∀ d e, w.dev = some d → v.dev = some e → d.nextKeypairId ≤ e.nextKeypairId)
    (keys : ∀ d, w.dev = some d → ∀ slot, slot < d.nextKeypairId →
      ∀ core, pool v slot = some core → pool w slot = some core) : Inv h v := by
  intro after device id pkt stored crypted
  have resident : (RxDisposition.nativeRxStore v).2 id = some pkt := by
    simp only [RxDisposition.nativeRxStore,device,Option.bind_some,stored]
  obtain ⟨old,stamp⟩ := packets id pkt resident crypted
  obtain ⟨prior,priorDevice,priorStored⟩ := Option.bind_eq_some_iff.mp old
  obtain ⟨bound,core,certificate,conditional⟩ := before prior priorDevice id pkt priorStored crypted
  exact ⟨Nat.lt_of_lt_of_le bound (frontier prior after priorDevice device),core,
    certificate.transport stamp,fun current resident =>
      conditional current (keys prior priorDevice pkt.keypair bound current resident)⟩

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
