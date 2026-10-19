import Leanux.Proofs.WG.Config.KeyStageModel
import Leanux.Proofs.WG.Config.GetterMetadataModel

/-! Header equalities of existing pure key-peer effect relations. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise TimerDiscipline
theorem invalidateDevice_header (d : Device) (kp : Option KeypairId) :
    sendConfiguration (invalidateDevice d kp)=sendConfiguration d := by
  cases kp with
  | none => rfl
  | some id => cases found : d.keypairs[id]? <;> simp [invalidateDevice,found,sendConfiguration]

theorem precomputeDevice_header (d : Device) (pid : PeerId) (p : Peer) :
    sendConfiguration (precomputeDevice d pid p)=sendConfiguration d := by
  cases has : d.staticIdentity.hasIdentity <;>
    cases ok : (curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2 <;>
    simp [precomputeDevice,has,ok,withPeer,sendConfiguration]

theorem peerUpdatedDevice_header (d : Device) (pid : PeerId) (p : Peer) (now : Int64) :
    sendConfiguration (peerUpdatedDevice d pid p now)=sendConfiguration d := by
  simp only [peerUpdatedDevice,expiredDevice,invalidateDevice_header]
  exact precomputeDevice_header d pid p

theorem keyReferenceRoundTrip_header (d : Device) (kp : Option KeypairId) :
    sendConfiguration (keyReferenceRoundTrip d kp)=sendConfiguration d := by
  cases kp with
  | none => rfl
  | some id =>
    cases found : d.keypairs[id]? with
    | none => simp [keyReferenceRoundTrip,found]
    | some k =>
      by_cases zero : k.refcount=0 <;> simp [keyReferenceRoundTrip,found,zero,withKeypair,sendConfiguration]

theorem fallbackDeviceAfterInspection_header (d : Device) (pid : PeerId) (p : Peer)
    (packets : List Packet) (now : Int64) (queued : Bool) :
    sendConfiguration (fallbackDeviceAfterInspection d pid p packets now queued)=sendConfiguration d := by
  dsimp only [fallbackDeviceAfterInspection,queuedDeviceAfterInspection]
  split
  · rfl
  · split <;> simp only [sendConfiguration,withPeer]

theorem stagedFallbackObservation_header (d : Device) (pid : PeerId) (p : Peer)
    (packets : List Packet) (observation : Int64 × Option Bool) (s : Campaign2.Snapshot)
    (effect : stagedFallbackObservation d pid p packets observation s) :
    s.wg.device.map sendConfiguration=some (sendConfiguration d) := by
  unfold stagedFallbackObservation at effect
  cases seen : observation.2 with
  | none =>
    simp only [seen] at effect
    rw [effect.1]
    rfl
  | some queued =>
    simp only [seen] at effect
    rw [effect.2.2]
    simp only [Option.map_some,fallbackDeviceAfterInspection_header]

theorem invalidStagedObservation_header (d : Device) (pid : PeerId) (p : Peer)
    (observation : Option (Int64 × Option Bool)) (s : Campaign2.Snapshot)
    (effect : invalidStagedObservation d pid p observation s) :
    s.wg.device.map sendConfiguration=some (sendConfiguration d) := by
  unfold invalidStagedObservation at effect
  split at effect
  · rw [effect.2]; rfl
  · obtain ⟨seen,_,actual⟩:=effect
    have h:=stagedFallbackObservation_header _ _ _ _ _ _ actual
    rw [keyReferenceRoundTrip_header] at h
    exact h

theorem keyPeerObservation_header (d : Device) (pid : PeerId) (p : Peer) (send : Bool)
    (observation : Option (Int64 × Option Bool)) (s : Campaign2.Snapshot)
    (effect : keyPeerObservation d pid p send observation s) :
    s.wg.device.map sendConfiguration=some (sendConfiguration d) := by
  obtain ⟨now,effect⟩:=effect
  cases send with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at effect
    rw [effect.2]
    simp only [Option.map_some,peerUpdatedDevice_header]
  | true =>
    simp only [ite_true] at effect
    simpa only [peerUpdatedDevice_header] using
      invalidStagedObservation_header _ _ _ _ _ effect

theorem observedKeyPeerRun_header (send : Bool) (d : Device) (pids : List PeerId)
    (observations : List (Option (Int64 × Option Bool))) (final : Device)
    (run : ObservedKeyPeerRun send d pids observations final) :
    sendConfiguration final=sendConfiguration d := by
  induction run with
  | nil => rfl
  | cons d pid p observation step next rest observations final resident effect device tail ih =>
    have same:=keyPeerObservation_header d pid p send observation step effect
    rw [device] at same
    exact ih.trans (Option.some.inj same)

end Leanux.Proofs.WG.Config

