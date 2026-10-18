import Leanux.Proofs.WG.Noise.DriverTagSilentFrames
import Leanux.Proofs.WG.Noise.DriverTagPeerConfigurationFrames
import Leanux.Proofs.WG.Queues.RxStackFrames
import Leanux.Proofs.WG.Queues.RxBorrow

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.DriverTags.Transmit
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

/-- Tag counterpart of CurrentSlots.lookupDst_view, projected directly from
the existing exact acquisition effect rather than a new lookup traversal. -/
theorem lookupDst_tag_frame (family addr : Nat) :
    SameView tagView (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView g))
    g ambient result final after rfl run
  change responseTagMap (wgStoreView final).dev = responseTagMap (wgStoreView g).dev
  cases result with
  | none =>
    change wgStoreView final = wgStoreView g at borrowed
    rw [borrowed]
  | some pid =>
    obtain ⟨d,p,device,resident,_,effect⟩ := borrowed
    rw [effect,device]
    exact tagMap_write d pid p _ resident rfl

/-- Tag counterpart of CurrentSlots.trim_preserves. The actual read remains
paired with its conditional staged-queue write; no saved arbitrary peer is framed. -/
theorem xmitTrim_tag_variant (pid : PeerId) :
    SameView tagView (xmitTrim pid) := by
  have step : SameView tagView (do
      let p ← getPeer pid
      if ← branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS) then
        setPeer pid {p with staged := p.staged.drop 1}
        modifyDev fun d => {d with txDropped := d.txDropped+1}
        pure (ForInStep.yield (PUnit.unit : PUnit.{1}))
      else pure (ForInStep.done (PUnit.unit : PUnit.{1}))) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro g ambient result final after run
    cases device : g.dev with
    | none =>
      simp [getPeer,getDev,device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases trim : p.staged.length > MAX_STAGED_PACKETS
        · simp [getPeer,getDev,device,resident,branch,AmbientM.branch,trim,
            setPeer,modifyDev] at run
          obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
          funext target
          simpa only [tagView,device,responseTagMap,Option.bind_some,List.drop_one] using
            congrFun (tagMap_write d pid p {p with staged := p.staged.drop 1} resident rfl) target
        · simp [getPeer,getDev,device,resident,branch,AmbientM.branch,trim] at run
          obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
          rfl
  intro initial
  change Preserves (fun g => tagView g = initial) (xmitTrim pid)
  unfold xmitTrim
  apply preserves_bind ((getPeer_frame pid).wp (fun s => s = initial))
  intro p
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind
    (list_view_spec tagView (fun s => s = initial) _ _ _ (fun _ _ => step.wp (fun s => s = initial)))
  intro _
  exact preserves_pure ()

/-- Tag counterpart of CurrentSlots.splice_preserves. The repeated original
read is reduced using its existing exact read/read source equation. -/
theorem xmitSplice_tag_variant (pid : PeerId) (packets : List Packet) :
    SameView tagView (xmitSplice pid packets) := by
  unfold xmitSplice
  rw [getPeer_twice]
  exact modifyPeer_frame pid (fun p => {p with staged := p.staged ++ packets}) (fun _ => rfl)

end Leanux.Proofs.WG.Noise.DriverTags.Transmit
