import Leanux.Proofs.WG.Noise.ResponseMacFrames
import Leanux.Proofs.WG.Lifetimes.DeviceControls

set_option autoImplicit false
/-! Physical purge/reset frames. -/
namespace Leanux.Proofs.WG.Noise.DriverTags.Control
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do

theorem purgeStagedPackets_tag_frame (pid : PeerId) :
    SameView (fun g => responseTagMap g.dev) (purgeStagedPackets pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [purgeStagedPackets,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [purgeStagedPackets,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      simp [purgeStagedPackets,getPeer,getDev,device,resident,modifyDev,setPeer] at run
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      funext target
      by_cases same : pid = target
      · subst target
        simp [responseTagMap,resident]
      · simp [responseTagMap,Std.TreeMap.getElem?_insert,same]

theorem resetLastSentHandshake_tag_frame (pid : PeerId) :
    SameView (fun g => responseTagMap g.dev) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  apply SameView.bind
  · exact fun initial => hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent)
      (fun g : WGWorld => responseTagMap g.dev = initial)
  · intro now
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro g ambient result final after run
    exact ResponseCaller.lastSent_tag_frame pid
      (now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64)
      g ambient result final after run

end Leanux.Proofs.WG.Noise.DriverTags.Control


