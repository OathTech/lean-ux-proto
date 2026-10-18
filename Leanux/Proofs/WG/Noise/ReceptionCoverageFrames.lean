import Leanux.Proofs.WG.Noise.ReceptionCallerClaims
import Leanux.Proofs.WG.Noise.ReceiveStepCallerClaims
import Leanux.Proofs.WG.Noise.TagCoverageModel
import Leanux.Proofs.WG.Noise.ResponseSuffixTagFrames
import Leanux.Proofs.WG.Noise.CookieReplyTagFrames
import Leanux.Proofs.WG.Noise.ReceptionTagFrames
import Leanux.Proofs.WG.Index.StagedSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ReceptionCaller
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Origins

def NativeCoverage (entry : TagMap) (history : List TagReceipt) (g : WGWorld) : Prop :=
  TagCoverage entry history (responseTagMap g.dev)

theorem lift_coverage_retained {α : Type} (entry : TagMap) (action : WG.M α)
    (frame : ∀ g ambient result final after,
      ((action.run g).run ambient) = .ok ((result, final), after) →
      TagsRetained (responseTagMap g.dev) (responseTagMap final.dev)) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · intro h g ambient pre; trivial
  · intro h g ambient result final after pre run
    exact pre.final_retained (frame g ambient result final after run)

theorem lift_coverage_exact {α : Type} (entry : TagMap) (action : WG.M α)
    (frame : ∀ g ambient result final after,
      ((action.run g).run ambient) = .ok ((result, final), after) →
      responseTagMap final.dev = responseTagMap g.dev) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (liftWGPrefix action) := by
  apply lift_coverage_retained entry action
  intro g ambient result final after run
  rw [frame g ambient result final after run]
  exact TagsRetained.refl _

theorem pure_coverage {α : Type} (entry : TagMap) (value : α) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (pure value : Obs α) :=
  StatePrefixEnsures.pure value (fun _ _ _ _ => True.intro) (fun _ _ _ prior => prior)

theorem ambient_coverage {α : Type} (entry : TagMap) (action : AmbientM α) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (liftWGPrefix (StateT.lift action : WG.M α)) := by
  apply lift_coverage_exact
  intro g ambient result final after run
  exact (ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant action
      (fun current => responseTagMap current.dev = responseTagMap g.dev))
      g ambient result final after rfl run

theorem peerUpdate_coverage (entry : TagMap) (pid : PeerId) (f : Peer → Peer)
    (tag : ∀ p, (f p).handshakeState = p.handshakeState) :
    StatePrefixPreserves (fun h g _ => NativeCoverage entry h g) (fun _ => True)
      (liftWGPrefix (do setPeer pid (f (← getPeer pid)))) := by
  apply lift_coverage_exact
  intro g ambient result final after run
  have effect := modifyPeer_spec_creationTagMap_variant g.dev pid f id
    (fun p => congrArg some (tag p)) g ambient result final after rfl run
  funext target
  simpa only [id_eq, ite_self] using effect target

theorem loadPhase_tag_frame (entry : Option Device) :
    Ensures Cookies.loadPhase
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  have frame := Cookies.loadPhase_sameStore.of_factor
    (fun v => responseTagMap v.dev) (fun g => responseTagMap g.dev) (fun _ => rfl)
  exact (ensures_iff _ _ _).mpr (frame (responseTagMap entry))

theorem gate_tag_frame (msg : List UInt8) (src : SkbSource) (entry : Option Device) :
    Ensures (gate msg src)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  unfold gate
  refine ensures_bind _ _ (loadPhase_tag_frame entry) ?_
  intro loaded
  refine ensures_bind _ _ (cookieValidatePacket_spec_tagMap_variant msg src loaded entry) ?_
  intro mac g ambient result final after pre run
  cases run
  exact pre

theorem observeGate_tags (msg : List UInt8) (src : SkbSource)
    (g : WGWorld) (ambient : Ambient) (r : GateReceipt)
    (final : WGWorld) (after : Ambient)
    (run : observeGate msg src g ambient = .ok ((r,final),after)) :
    r.before.tagAt = responseTagMap g.dev ∧
    r.after.tagAt = responseTagMap g.dev ∧
    responseTagMap final.dev = responseTagMap g.dev := by
  change ((((gate msg src).run g).run ambient).map _) = _ at run
  cases actual : ((gate msg src).run g).run ambient with
  | error stop => simp only [actual,Except.map] at run; cases run
  | ok out =>
    obtain ⟨⟨⟨loaded,mac⟩,next⟩,inputs⟩ := out
    simp only [actual,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    have frame := gate_tag_frame msg src g.dev g ambient (loaded,mac) next inputs rfl actual
    exact ⟨rfl,frame,frame⟩

end Leanux.Proofs.WG.Noise.ReceptionCaller
