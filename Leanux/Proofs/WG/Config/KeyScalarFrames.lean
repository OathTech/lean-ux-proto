import Leanux.Proofs.WG.Config.KeyScalarEffects
import Leanux.Proofs.WG.Config.GetterScalarSource
import Leanux.Proofs.WG.Config.KeyStageSource

/-! Physical getter-scalar retention through identity, cookie, precompute, expiry, acquisition and staged work. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration
theorem identity (key : Key) : SameView view (setStaticIdentityPrivateKey key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  cases hd : g.dev with
  | none=>
    simp [setStaticIdentityPrivateKey,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d=>
    have source:=setStaticIdentity_run key d g a hd
    rw [run] at source
    cases source
    simp only [view,hd]
    rfl

theorem cookie : SameView view cookiePrecomputeDeviceKeys := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  cases hd : g.dev with
  | none=>
    simp [cookiePrecomputeDeviceKeys,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d=>
    have source:=cookiePrecompute_run d g a hd
    rw [run] at source
    cases source
    simp only [view,hd]
    rfl

theorem precompute (pid : PeerId) : SameView view (precomputeStaticStatic pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  cases hd : g.dev with
  | none=>
    simp [precomputeStaticStatic,requireNotPending,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d=>
    cases hp:d.peers[pid]? with
    | none=>
      simp [precomputeStaticStatic,requireNotPending,getPeer,getDev,hd,hp,invariant,AmbientM.invariant] at run
      cases run
    | some p=>
      have source:=precomputeStaticStatic_run pid d p hp g a hd
      rw [run] at source
      cases source
      simp only [view,hd]
      unfold precomputeDevice
      split
      · dsimp only
        split
        · exact write_values d pid p _ hp rfl
        · funext target
          by_cases eq : target=pid
          · subst target
            simp [GetterScalar.values,withPeer,GetterScalar.cell,hp]
          · simp [GetterScalar.values,withPeer,Std.TreeMap.getElem?_insert,Ne.symm eq]
      · dsimp only
        exact write_values d pid p _ hp rfl

theorem expire (pid : PeerId) : SameView view (expireCurrentPeerKeypairs pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  have cut:=run
  unfold expireCurrentPeerKeypairs at cut
  simp only [requireNotPending,pure_bind] at cut
  rw [MaterialOrigin.bind_ok_ambient] at cut
  obtain ⟨_,u,c,clear,_⟩:=cut
  cases hd:g.dev with
  | none=>
    simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,hd,invariant,AmbientM.invariant] at clear
    cases clear
  | some d=>
    cases hp:d.peers[pid]? with
    | none=>
      simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,hd,hp,invariant,AmbientM.invariant] at clear
      cases clear
    | some p=>
      obtain ⟨now,ending⟩:=expireCurrent_exact pid d p hp g a ret v b hd run
      unfold view
      rw [ending,hd]
      exact expired_values pid d p now hp

theorem lookup (key : Key) : SameView view (pubkeyLookup key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  apply (Index.pubkeyLookup_preserves_acquire_world_source key
    (fun w=>view w=view g) ?_ g a ret v b rfl run).1
  intro w d pid p device resident pre
  change values (some (Index.acquirePeer d pid p))=view g
  have same:=write_values d pid p {p with refcount:=p.refcount+1} resident rfl
  exact same.trans (by simpa only [view,device] using pre)

theorem staged (entry : Map) (pid : PeerId) :
    Ensures (sendStagedPackets pid) (Retained entry) (fun _=>Retained entry) := by
  intro g a ret v b pre run
  have kept:=rich_retained (Index.StagingRich.sendStagedPackets_rich pid g g a ret v b
    (Index.StagingRich.refl g) run)
  exact fun target cell found=>pre target cell (kept target cell found)
end Leanux.Proofs.WG.Config.GetterScalar
