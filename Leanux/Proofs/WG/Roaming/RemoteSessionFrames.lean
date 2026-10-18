import Leanux.Proofs.WG.Roaming.RemoteSessionEffects
import Leanux.Proofs.WG.Queues.RxCleanupProtection

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing TimerDiscipline Std.Do

theorem beginSession_endpoints (pid : PeerId) : SameView destinationAt (beginSession pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient ok out after run
  cases device : g.dev with
  | none =>
    simp [beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [beginSession,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨final,ending,effect⟩ := beginSession_effect pid d p g.keypairCounter resident
        g ambient ok out after ⟨device,rfl⟩ run
      apply endpointMap_destinations
      rw [ending,device]
      exact sessionEffect_endpoints pid d p g.keypairCounter out.keypairCounter ok final resident effect

theorem peerPut_remotes (peer : Option PeerId) (entry : RemoteMap) :
    Ensures (peerPut peer) (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) := by
  intro g ambient result final after pre run
  cases result
  cases peer with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact pre
  | some pid =>
    cases device : g.dev with
    | none =>
      simp [peerPut,requireNotPending,branch,AmbientM.branch,getPeer,getDev,
        device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [peerPut,requireNotPending,branch,AmbientM.branch,getPeer,getDev,
          device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        have positive := (Queues.RxCredits.peerPut_effect pid g final d p ambient after
          device resident run).1
        have ending := Index.peerPut_normal_device pid d p resident positive
          g final ambient after () device run
        intro target remote present
        apply pre target remote
        have kept := releasedPeerDevice_remotes d pid p resident target remote
          (by simpa [destinationAt,peerAt,ending] using present)
        simpa [destinationAt,peerAt,device] using kept

theorem remotes_snapshot (g : WGWorld) (ambient : Ambient) :
    remoteMap (Campaign2.snapshot g ambient) = destinationAt g := rfl

end Leanux.Proofs.WG.Roaming
