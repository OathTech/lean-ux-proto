import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialPrepareFrames

/-! The packet certificate exposes the actual decrypting allocation. A later
resident key is related by the carrier's conditional equality; numeric-slot
agreement alone is never substituted for allocation identity. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity AuthenticatedEffects Responder
variable {id : SkbId}

/-- Exact earlier AEAD input and output, now with the certificate's allocation
identity rather than only a numeric key slot. -/
theorem Certificate.native_aead (certificate : Certificate h id pkt w core) :
    ∃ pre post, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      h = pre ++ .receipt (.decrypt id r) :: post ∧
      Published id r out pid published ambient ∧ pkt = {out with state := .crypted} ∧
      ∃ d key, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
        d.keypairs[r.value.1.keypair]? = some key ∧ key.internalId = core.allocation ∧
        key.receiving.isValid = true ∧ pkt.keypair = r.value.1.keypair ∧
        pkt.nonce = u64le r.value.1.bytes 8 ∧
        aeadDecrypt key.receiving.key (counterNonce pkt.nonce) (r.value.1.bytes.drop 16) [] = some pkt.bytes := by
  obtain ⟨pre,post,r,out,pid,published,ambient,position,pub,packet,stamp,material⟩ := certificate
  obtain ⟨d,key,hd,hp,hk,valid,decrypt,record,aead⟩ := RxOrigin.decrypt_receipt id r out pub.1 pub.2.1
  have slot : out.keypair = r.value.1.keypair := by
    have projected := congrArg RxPacket.keypair record
    exact projected
  have nonce : out.nonce = u64le r.value.1.bytes 8 := by
    have projected := congrArg RxPacket.nonce record
    exact projected
  have actualCore : keyCore key = core := by
    simpa only [pool,hd,Option.bind_some,packet,slot,hk,Option.map_some,Option.some.injEq] using material
  refine ⟨pre,post,r,out,pid,published,ambient,position,pub,packet,d,key,hd,hp,hk,
    congrArg KeyCore.allocation actualCore,valid,?_,?_,?_⟩
  · simpa only [packet] using slot
  · simpa only [packet] using nonce
  · simpa only [packet,nonce] using aead

/-- The carrier selects the exact historical authenticating allocation for
an actual crypted cell and a successful current resident-key read. -/
theorem Inv.resident (hi : Inv h w) (resident : (RxDisposition.nativeRxStore w).2 id = some pkt)
    (crypted : pkt.state = .crypted) (key : Keypair)
    (read : (w.dev.bind fun d => d.keypairs[pkt.keypair]?) = some key) :
    Certificate h id pkt w (keyCore key) := by
  obtain ⟨d,device,cell⟩ := Option.bind_eq_some_iff.mp resident
  obtain ⟨bound,core,certificate,conditional⟩ := hi d device id pkt cell crypted
  have same := conditional (keyCore key) (by simp only [pool,read,Option.map_some])
  simpa only [same] using certificate

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
