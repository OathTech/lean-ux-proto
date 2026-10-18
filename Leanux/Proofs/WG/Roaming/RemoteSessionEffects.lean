import Leanux.Proofs.WG.Roaming.RemoteRetentionModel
import Leanux.Proofs.WG.Roaming.ResponseRejectionFrames
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Noise.RotationEffects
import Leanux.Proofs.WG.Index.RetirementReleaseSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing TimerDiscipline Std.Do

theorem endpointMap_destinations {a b : WGWorld}
    (same : responseEndpointMap b.dev = responseEndpointMap a.dev) :
    destinationAt b = destinationAt a := by
  funext pid
  have point := congrFun same pid
  change (((b.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination) =
    (((a.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination)
  simpa only [responseEndpointMap, Option.bind_map, Function.comp_def, id_def] using
    congrArg (fun x : Option (Option Endpoint) => (x.bind id).map destination) point

theorem rotationRun_endpoints {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (steps : RotationRun pid d actions final) :
    responseEndpointMap (some final) = responseEndpointMap (some d) := by
  induction steps with
  | nil => rfl
  | write d final change p rest resident tail ih =>
    exact ih.trans ((pinned_const _private.Leanux.Proofs.WG.Roaming.ResponseRejectionFrames.«0».Leanux.Proofs.WG.Roaming.endpoint_write)
      d pid p (change.apply p) resident (by cases change <;> rfl))
  | put d middle final key rest release tail ih =>
    apply ih.trans
    funext target
    simp only [responseEndpointMap,Option.bind_some,clearPut_peers release]

theorem sessionPrepared_endpoints (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (birth : Int64) (resident : d.peers[pid]? = some p) :
    responseEndpointMap (some (sessionPrepared pid d p counter birth)) =
      responseEndpointMap (some d) := by
  change responseEndpointMap (some {d with
    keypairs := (sessionDerivedDevice (Index.createdDevice d counter p.handshakeEntryPeer)
      d.nextKeypairId p { internalId := counter + 1, peer := p.handshakeEntryPeer }
      p.handshakeState birth).keypairs
    nextKeypairId := d.nextKeypairId + 1
    peers := d.peers.insert pid (sessionZeroPeer p)}) = _
  funext target
  by_cases same : pid = target
  · subst target
    simp [responseEndpointMap,resident,sessionZeroPeer]
  · simp [responseEndpointMap,Std.TreeMap.getElem?_insert,same]

theorem sessionEffect_endpoints (pid : PeerId) (d : Device) (p : Peer)
    (counter finalCounter : Nat) (ok : Bool) (final : Device)
    (resident : d.peers[pid]? = some p)
    (effect : SessionEffect pid d p counter ok final finalCounter) :
    responseEndpointMap (some final) = responseEndpointMap (some d) := by
  cases ok with
  | false => rw [effect.1]
  | true =>
    obtain ⟨_,_,_,_,birth,rotated,steps,_,rfl⟩ := effect
    change responseEndpointMap (some rotated) = _
    exact (rotationRun_endpoints steps).trans
      (sessionPrepared_endpoints pid d p counter birth resident)

theorem releasedPeerDevice_remotes (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    RemoteRetained (fun target => (d.peers[target]?.bind Peer.endpoint).map destination)
      (fun target => ((Index.releasedPeerDevice d pid p).peers[target]?.bind Peer.endpoint).map destination) := by
  intro target remote found
  by_cases last : p.refcount = 1
  · by_cases same : pid = target
    · subst target
      simp [Index.releasedPeerDevice,last] at found
    · simpa [Index.releasedPeerDevice,last,Std.TreeMap.getElem?_erase,
        Std.TreeMap.getElem?_insert,same] using found
  · by_cases same : pid = target
    · subst target
      simpa [Index.releasedPeerDevice,last,resident] using found
    · simpa [Index.releasedPeerDevice,last,Std.TreeMap.getElem?_insert,same] using found

end Leanux.Proofs.WG.Roaming
