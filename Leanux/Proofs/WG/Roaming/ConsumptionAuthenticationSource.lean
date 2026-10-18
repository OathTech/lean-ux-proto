import Leanux.Proofs.WG.Roaming.ConsumptionAuthenticationBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes Noise.ConsumeConfirmation Noise.ConfirmationOrder

theorem consumption_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (q : Record) (occurs : OccursAt trace placeholders q) :
    ∃ e : ConsumptionAuthentication, e.Valid trace placeholders q ∧ e.Facts q := by
  obtain ⟨pre,post,r,position,index,matched⟩ := occurs
  obtain ⟨before,after,decrypt,out,pid,published,ambient,earlier,publication,certificate⟩ :=
    PublicationRunner.consumed trace placeholders pre post q.occurrence q.skb q.packetStamp r position
  have kept := matched
  obtain ⟨valid,c,allocation,source,key,qeq⟩ := matched
  have obsEq : q.observation = projects r c := congrArg Record.observation qeq
  obtain ⟨material,ctx,current,peer,member,mvalid,mvalue,configured,hcurrent,hpeer,identity⟩ :=
    certificate.owner_identity
  obtain ⟨d,k,p,afterDev,hd,hpkt,hkey,keyValid,owner,support,shape,aead,rest⟩ :=
    certificate.2.1.1
  have endpoint := ConsumedEndpoint.initialized_endpoint trace placeholders pre post
    q.occurrence q.skb q.packetStamp r position
  have endpointFamily : r.endpoint.family = AF_INET ∨ r.endpoint.family = AF_INET6 := by
    rw [endpoint.1]
    rcases endpoint.2 with ipv4 | ipv6
    · exact Or.inl (by simp [sourceEndpoint,ipv4])
    · exact Or.inr (by simp [sourceEndpoint,ipv6])
  have dest := setPeerEndpoint_destination r.peer r.endpoint endpointFamily
    r.run.before r.run.ambientBefore () c.before c.ambientBefore True.intro source.1
  let e : ConsumptionAuthentication :=
    ⟨before.length,Campaign2.snapshot decrypt.before decrypt.ambientBefore,
      decrypt.value.1,k,Campaign2.snapshot material.before material.ambientBefore,ctx,peer⟩
  have peerAt : q.observation.entry.peerAt q.observation.peer = some peer := by
    rw [obsEq]
    change (r.run.before.dev.bind fun d => d.peers[r.peer]?) = some peer
    simp only [hcurrent,Option.bind_some,hpeer]
  have keyAt : (decrypt.before.dev.bind fun d => d.keypairs[decrypt.value.1.keypair]?) = some k := by
    simp only [hd,Option.bind_some,hkey]
  refine ⟨e,?_,?_⟩
  · exact ⟨pre,post,before,after,r,decrypt,out,pid,published,ambient,material,
      position,index,kept,earlier,publication,certificate,member,mvalid,mvalue,configured,
      rfl,rfl,rfl,keyAt,rfl,peerAt,identity⟩
  · have order : before.length < q.position := by
      rw [index,earlier,List.length_append,List.length_cons]
      omega
    have packet := certificate.2.2.1
    obtain ⟨sessionDev,sessionDevice,sessionPeer,registered,alive,word⟩ := configured
    refine ⟨order,?_,keyAt,keyValid,?_,?_,?_,?_,?_,?_,peerAt,?_,alive,?_,identity⟩
    · change (decrypt.before.dev.bind fun d => d.rxSkbs[q.skb]?) = some decrypt.value.1
      simp only [hd,Option.bind_some,hpkt]
    · simpa only [obsEq,projects] using certificate.1.2.2
    · rw [obsEq]
      change r.packet = {decrypt.value.1 with nonce := u64le decrypt.value.1.bytes 8, bytes := r.packet.bytes, state := .crypted}
      rw [packet,shape]
    · rw [obsEq]
      change _ = some r.packet.bytes
      simpa only [packet] using aead
    · simpa only [obsEq,projects] using endpoint.1
    · simpa only [obsEq,projects] using endpoint.2
    · rw [obsEq]
      change destinationAt c.before r.peer = some (destination (sourceEndpoint r.packet.source))
      simpa only [endpoint.1] using dest
    · refine ⟨sessionDev,sessionDevice,?_,?_⟩
      · simpa only [obsEq,projects] using sessionPeer
      · simpa only [obsEq,projects] using registered
    · simpa only [obsEq,projects] using word


end Leanux.Proofs.WG.Roaming
