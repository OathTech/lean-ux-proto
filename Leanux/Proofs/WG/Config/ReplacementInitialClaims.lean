import Leanux.Proofs.WG.Config.ReplacementInitialSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

private abbrev replaceInitialPrefix := noise_const _private.Leanux.Proofs.WG.Config.ReplacePeersRequestSource.«0».Leanux.Proofs.WG.Config.replacePeersPrefix

/-- Initial representation and residency assumptions justify the real free
and dead-marking cuts of a complete flag-only replacement request. -/
theorem observedReplacePeers_initial (d : Device) (t4 t6 : AllowedIps.Tree)
    (hi : AllowedIps.RoutingInvariant d t4 t6) (pairs : NodePairs d)
    (listed : ListedResidents d d.peerList) :
    Campaign2.Product.Ensures (observedReplacePeers (byIndex d))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s.toSnapshot d)
      (fun result _ => ∃ cut, result = (some cut, 0) ∧
        AllowedIps.Cleared (requestGeneration d) cut.afterFree ∧
        cut.afterFree.peerList = d.peerList ∧
        ∃ marked, cut.afterMark.wg.device = some marked ∧
          DeadPassEffect cut.afterFree d.peerList marked ∧
          ∀ pid ∈ d.peerList, ∃ p, marked.peers[pid]? = some p ∧ p.isDead = true) := by
  have routing : AllowedIps.RoutingInvariant (requestGeneration d) t4 t6 :=
    ⟨hi.forest,hi.valid4,hi.valid6,hi.compressed4,hi.compressed6,
      hi.nodup4,hi.nodup6,hi.below,hi.lists,hi.owners,hi.peerSlots⟩
  have hprefix : Noise.Product.Ensures (liftWG (replaceInitialPrefix (byIndex d)))
      (fun w => w.wg.dev = some d ∧ selectsDevice w.wg d)
      (fun ret w => ret = .ok () ∧ w.wg.dev = some (requestGeneration d)) := by
    intro w result final pre run
    rw [Framing.liftWG_run] at run
    cases native : ((replaceInitialPrefix (byIndex d)).run w.wg).run w.ambient with
    | error err => simp only [native,Except.map] at run; cases run
    | ok pair =>
      obtain ⟨⟨ret,g⟩,ambient⟩ := pair
      simp only [native,Except.map] at run
      cases run
      exact replacePeersPrefix_generation d w.wg w.ambient result g ambient pre native
  have carried : Noise.Product.Ensures (observedReplacePeers (byIndex d))
      (fun w => w.wg.dev = some d ∧ selectsDevice w.wg d)
      (fun result _ => ∀ cut, result.1 = some cut →
        AllowedIps.Cleared (requestGeneration d) cut.afterFree) := by
    change Noise.Product.Ensures
      (liftWG (replaceInitialPrefix (byIndex d)) >>= fun selected =>
        match selected with
        | .error e => pure (none,e)
        | .ok () => do
          let cut ← observedRemoveAll
          let ret ← liftWG (noise_const _private.Leanux.Proofs.WG.Config.ReplacePeersRequestSource.«0».Leanux.Proofs.WG.Config.replacePeersSuffix)
          pure (some cut,ret)) _ _
    refine Noise.Product.ensures_bind _ _ hprefix ?_
    intro selected
    cases selected with
    | error e =>
      intro w result final pre run
      cases pre.1
    | ok u =>
      cases u
      have removed : Noise.Product.Ensures observedRemoveAll
          (fun w => Except.ok () = (Except.ok () : Except Int Unit) ∧
            w.wg.dev = some (requestGeneration d))
          (fun cut _ => AllowedIps.Cleared (requestGeneration d) cut.afterFree) := by
        intro w cut final pre run
        exact observedRemoveAll_cleared (requestGeneration d) t4 t6 routing
          w cut final pre.2 run
      refine Noise.Product.ensures_bind _ _ removed ?_
      intro cut
      refine Noise.Product.ensures_bind _ _
        (fun w ret final pre run => pre) ?_
      intro ret w result final pre run other same
      cases run
      cases same
      exact pre
  intro w result final pre run
  obtain ⟨cut,rfl,facts⟩ := observedReplacePeers_selected d w result final pre run
  have hc := carried w (some cut,0) final pre run cut rfl
  obtain ⟨postPairs,postListed,listEq⟩ :=
    cleared_removeAll_inputs (requestGeneration d) cut.afterFree hc pairs listed
  obtain ⟨marked,device,effect,dead⟩ := facts postPairs postListed
  exact ⟨cut,rfl,hc,listEq,marked,device,by simpa only [listEq, requestGeneration] using effect,
    by simpa only [listEq, requestGeneration] using dead⟩

end Leanux.Proofs.WG.Config
