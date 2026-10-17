import Leanux.Proofs.WG.Config.ReadbackSource
import Leanux.Proofs.WG.Noise.AccessSource
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

theorem clearEndpointSource_readbackFrame (pid : PeerId) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (clearPeerEndpointSrc pid) (fun w => readbackFrame w sock fixtures)
      (fun _ w => readbackFrame w sock fixtures) := by
  let P : WGWorld → Prop := fun g => readbackFrame g sock fixtures
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
