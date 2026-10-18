import Leanux.Proofs.WG.Roaming.RemotePeerFrames
import Leanux.Proofs.WG.Roaming.RemoteRetentionModel
import Leanux.Proofs.WG.Roaming.EndpointClaims
import Leanux.Proofs.WG.Config.EndpointSetSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing Std.Do

theorem setPeerEndpoint_remotes (pid : PeerId) (e : Endpoint)
    (valid : e.family = AF_INET ∨ e.family = AF_INET6) (entry : RemoteMap) :
    Ensures (setPeerEndpoint pid e) (fun g => destinationAt g = entry)
      (fun _ g => destinationAt g = updateRemote entry pid (destination e)) := by
  intro g ambient result final after pre run
  have selected := setPeerEndpoint_destination pid e valid g ambient result final after trivial run
  cases device : g.dev with
  | none =>
    simp [setPeerEndpoint,requireNotPending,getPeer,getDev,device,
      invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [setPeerEndpoint,requireNotPending,getPeer,getDev,device,resident,
        invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨reset,ending,_,_⟩ := Config.setPeerEndpoint_exact pid e d p resident
        valid g.nlSock7 g.fixtureNetDevices g ambient result final after
        ⟨device,rfl,rfl⟩ run
      funext target
      by_cases same : target = pid
      · subst target
        simpa only [updateRemote,ite_true] using selected
      · have other : destinationAt final target = destinationAt g target := by
          rw [show destinationAt final target =
            ((final.dev.bind fun dd => dd.peers[target]?).bind Peer.endpoint).map destination from rfl,
            ending]
          change ((some (Config.endpointStores d pid p e reset)).bind
            (fun dd => dd.peers[target]?) |>.bind Peer.endpoint |>.map destination) = _
          unfold Config.endpointStores
          split
          · simp [destinationAt,peerAt,device]
          · cases reset <;>
              simp [Config.withPeer,destinationAt,peerAt,device,Std.TreeMap.getElem?_insert,
                Ne.symm same]
        simpa only [updateRemote,same,ite_false] using other.trans (congrFun pre target)

theorem setPeerEndpointFromSkb_remotes (pid : PeerId) (src : SkbSource) (entry : RemoteMap) :
    Ensures (setPeerEndpointFromSkb pid src) (fun g => destinationAt g = entry)
      (fun _ g => destinationAt g = updateRemote entry pid (destination (sourceEndpoint src))) := by
  unfold setPeerEndpointFromSkb
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (endpointFromSkb_exact src (fun g => destinationAt g = entry))) ?_
  intro endpoint g ambient result final after pre run
  obtain ⟨kept,rfl,_⟩ := pre
  have valid : (sourceEndpoint src).family = AF_INET ∨
      (sourceEndpoint src).family = AF_INET6 := by
    unfold sourceEndpoint
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  let next := {ambient with steps := ambient.steps.push {
    decision := .epFromSkbOk, outcome := true, netRx := ambient.netRxSection}}
  have actual : ((setPeerEndpoint pid (sourceEndpoint src)).run g).run next =
      .ok ((result,final),after) := by
    simpa [branch,AmbientM.branch,next] using run
  exact setPeerEndpoint_remotes pid _ valid entry g next result final after kept actual

end Leanux.Proofs.WG.Roaming
