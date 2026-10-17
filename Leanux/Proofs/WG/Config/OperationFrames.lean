import Leanux.Proofs.WG.Config.Model
import Leanux.Proofs.WG.Config.BranchSource
import Leanux.Proofs.WG.Roaming.Frames

/-! Preservation support separated from configuration effects and public claims.
The remaining frames describe updates within the WireGuard state. -/
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def portState (g : WGWorld) : Option (Nat × Option Nat × Option Nat × Bool) :=
  g.dev.map fun d => (d.incomingPort, d.sock4, d.sock6, d.running)

theorem clearEndpointSource_device_frame (pid : PeerId) (initial : Option Device) :
    ⦃fun w => ⌜w.dev.map withoutPeers = initial⌝⦄ clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜w.dev.map withoutPeers = initial⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let P : WGWorld → Prop := fun g => g.dev.map withoutPeers = initial
  have hpure : Ensures (pure () : WG.M Unit) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hget : Ensures (get : WG.M WGWorld) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient p final after pre run).1
  have hset (p : Peer) : Ensures (setPeer pid p) P (fun _ => P) := by
    intro g ambient result final after pre run
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid p})}), ambient) = _ at run
    cases run
    cases hd : g.dev <;> simpa [P, hd, withoutPeers] using pre
  have hmodify (f : Peer → Peer) :
      Ensures (getPeer pid >>= fun p => setPeer pid (f p)) P (fun _ => P) :=
    ensures_bind _ _ hread (fun p => hset (f p))
  have hreset : Ensures (dstCacheReset pid) P (fun _ => P) := by
    unfold dstCacheReset
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (get : AmbientM Ambient) P)
    · intro ambient
      refine ensures_bind (Q := fun _ => P) _ _ hget ?_
      intro g
      split
      · exact hpure
      · refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
        · exact (ensures_iff _ _ _).mpr
            (hoare_liftAmbient_variant (AmbientM.hiddenJiffies .dstCacheResetTs) P)
        · intro ts
          exact hmodify (fun p => {p with dstCache := {p.dstCache with resetTs := ts}})
  unfold clearPeerEndpointSrc dstCacheResetNow
  refine ensures_bind (Q := fun _ => P) _ _ hread ?_
  intro p
  refine ensures_bind (Q := fun _ => P) _ _ (hset _) ?_
  intro _
  refine ensures_bind (Q := fun _ => P) _ _ hreset ?_
  intro _
  exact hmodify (fun p => {p with dstCache := {p.dstCache with slot := none}})

theorem clearPeerEndpointSrc_port_spec (pid : PeerId)
    (initial : Option (Nat × Option Nat × Option Nat × Bool)) :
    ⦃fun w => ⌜portState w = initial⌝⦄ clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜portState w = initial⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  have hd := (ensures_iff _ _ _).mpr (clearEndpointSource_device_frame pid (g.dev.map withoutPeers))
    g ambient result final after rfl run
  have hp := congrArg (fun x : Option Device => x.map fun d =>
    (d.incomingPort, d.sock4, d.sock6, d.running)) hd
  have same : portState final = portState g := by
    simpa [portState, withoutPeers, Option.map_map, Function.comp_def] using hp
  exact same.trans pre

theorem clearEndpointSource_portBound (pid : PeerId) (bound : Nat → Bool) :
    Ensures (clearPeerEndpointSrc pid) (fun w => w.portBound = bound)
      (fun _ w => w.portBound = bound) := by
  let P : WGWorld → Prop := fun g => g.portBound = bound
  have hpure : Ensures (pure () : WG.M Unit) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hget : Ensures (get : WG.M WGWorld) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient p final after pre run).1
  have hset (p : Peer) : Ensures (setPeer pid p) P (fun _ => P) := by
    intro g ambient result final after pre run
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid p})}), ambient) = _ at run
    cases run
    exact pre
  have hmodify (f : Peer → Peer) :
      Ensures (getPeer pid >>= fun p => setPeer pid (f p)) P (fun _ => P) :=
    ensures_bind _ _ hread (fun p => hset (f p))
  have hreset : Ensures (dstCacheReset pid) P (fun _ => P) := by
    unfold dstCacheReset
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (get : AmbientM Ambient) P)
    · intro ambient
      refine ensures_bind (Q := fun _ => P) _ _ hget ?_
      intro g
      split
      · exact hpure
      · refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
        · exact (ensures_iff _ _ _).mpr
            (hoare_liftAmbient_variant (AmbientM.hiddenJiffies .dstCacheResetTs) P)
        · intro ts
          exact hmodify (fun p => {p with dstCache := {p.dstCache with resetTs := ts}})
  unfold clearPeerEndpointSrc dstCacheResetNow
  refine ensures_bind (Q := fun _ => P) _ _ hread ?_
  intro p
  refine ensures_bind (Q := fun _ => P) _ _ (hset _) ?_
  intro _
  refine ensures_bind (Q := fun _ => P) _ _ hreset ?_
  intro _
  exact hmodify (fun p => {p with dstCache := {p.dstCache with slot := none}})

end Leanux.Proofs.WG.Config
