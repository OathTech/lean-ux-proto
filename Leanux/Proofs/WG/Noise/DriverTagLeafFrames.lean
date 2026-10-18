import Leanux.Proofs.WG.Noise.DriverTagSource
import Leanux.Proofs.WG.Noise.PendingConfigurationFrames
import Leanux.Proofs.WG.Noise.ReceptionCoverageFrames
import Leanux.Proofs.WG.Config.Precomputation

/-! Tag projections of existing store/configuration/socket frames. Actual peer
reads stay paired with writes; no arbitrary replacement-peer premise is used. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes

def tagView (g : WGWorld) : TagMap := responseTagMap g.dev

theorem store_frame {α : Type} {action : WG.M α} (frame : SameWGStore action) :
    SameView tagView action :=
  frame.of_factor (fun s => responseTagMap s.dev) tagView (fun _ => rfl)

theorem socket_frame {α : Type} {action : WG.M α} (frame : SameSocket action) :
    SameView tagView action := by
  apply frame.of_factor (fun s => responseTagMap s.dev) tagView
  intro g
  change responseTagMap g.dev = responseTagMap (g.dev.map socketDevice)
  cases g.dev <;> rfl

theorem configuration_frame {α : Type} {action : WG.M α} (frame : SameConfiguration action) :
    SameView tagView action := by
  apply frame.of_factor (fun s => responseTagMap s.dev) tagView
  intro g
  change responseTagMap g.dev = responseTagMap (g.dev.map configurationDevice)
  cases g.dev <;> rfl

theorem ambient_frame {α : Type} (action : AmbientM α) :
    SameView tagView (StateT.lift action : WG.M α) := by
  apply SameView.of_wp
  intro initial
  exact hoare_liftAmbient action _

theorem getPeer_frame (pid : PeerId) : SameView tagView (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient p final after run
  exact congrArg tagView (Peers.getPeer_current pid g final p ambient after run).1

theorem modifyDev_frame (f : Device → Device)
    (same : ∀ d, responseTagMap (some (f d)) = responseTagMap (some d)) :
    SameView tagView (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases run
  change responseTagMap (g.dev.map f) = responseTagMap g.dev
  cases device : g.dev with
  | none => rfl
  | some d => exact same d

theorem modifyPeer_frame (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).handshakeState = p.handshakeState) :
    SameView tagView (do setPeer pid (f (← getPeer pid))) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have effect := modifyPeer_spec_creationTagMap_variant g.dev pid f id
    (fun p => congrArg some (same p)) g ambient result final after rfl run
  funext target
  simpa only [tagView,id_eq, ite_self] using effect target

theorem pubkeyLookup_frame (key : Key) : SameView tagView (pubkeyLookup key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact (pubkeyLookup_spec_initiationTagMap_variant key g.dev
    g ambient result final after rfl run).1

theorem peerGet_frame (pid : PeerId) : SameView tagView (peerGet pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [peerGet,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [peerGet,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := ((ensures_iff _ _ _).mpr (Config.peerGet_exact pid d p resident)
        g ambient result final after device run).1
      change responseTagMap final.dev = responseTagMap g.dev
      rw [effect,device]
      exact tagMap_write d pid p _ resident rfl

theorem precomputeStaticStatic_frame (pid : PeerId) :
    SameView tagView (precomputeStaticStatic pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [precomputeStaticStatic,requireNotPending,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [precomputeStaticStatic,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨value,out,tail,execution,effect⟩ :=
        Config.precomputeStaticStatic_returns pid d p resident g ambient device
      rw [run] at execution
      cases execution
      change responseTagMap final.dev = responseTagMap g.dev
      rw [effect,device]
      unfold Config.precomputeDevice
      split
      · dsimp only
        split
        · exact tagMap_write d pid p _ resident rfl
        · funext target
          by_cases same : pid = target
          · subst target
            simp [responseTagMap,Config.withPeer,resident]
          · simp [responseTagMap,Config.withPeer,Std.TreeMap.getElem?_insert,same]
      · exact tagMap_write d pid p _ resident rfl

theorem lift_frame {α : Type} (entry : TagMap) (action : WG.M α)
    (frame : SameView tagView action) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix action) :=
  lift_exact entry action ((ProjectedAction.iff_run_ambient _ _ _).mp frame)

theorem ambient_preserves {α : Type} (entry : TagMap) (action : AmbientM α) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix (StateT.lift action : WG.M α)) :=
  lift_frame entry _ (ambient_frame action)

end Leanux.Proofs.WG.Noise.DriverTags
