import Leanux.Proofs.WG.Index.OwnerCoherenceRetransmitFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceCallbackFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceQueuedClaims
import Leanux.Proofs.WG.TimerDiscipline.RetrySource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Every normal original retransmit callback preserves hashed-owner coherence,
across retry and give-up, arbitrary records and wheel states. No successful arm,
queue acquisition, slot consistency or reference budget is assumed. -/
theorem expiredRetransmitHandshake_owner_coherent (pid : PeerId) :
    Campaign2.Ensures (expiredRetransmitHandshake pid) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  let safe : WGWorld → Prop := fun g => ∀d, g.dev = some d → HashedOwnersCoherent d
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) safe (fun _ => safe) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) safe (fun _ => safe) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action safe)
  have hread : Ensures (getPeer pid) safe (fun _ => safe) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid safe)
      g ambient result final after pre run).1
  have increment : Ensures (do
      let p ← getPeer pid
      setPeer pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1}) safe
      (fun _ => safe) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid safe)) ?_
    intro p g ambient result final after pre run
    cases device : g.dev with
    | none => simp [peerAt,device] at pre
    | some d =>
      have resident : d.peers[pid]? = some p := by simpa [peerAt,device] using pre.2
      simp [setPeer,modifyDev,device] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      intro actual found
      cases found
      exact peerWrite_owner_coherent d pid p _ resident rfl rfl (pre.1 d device)
  have giveUp : Ensures (TimerDiscipline.retransmitGiveUp pid) safe (fun _ => safe) := by
    unfold TimerDiscipline.retransmitGiveUp
    refine ensures_bind _ _ (delTimer_spec_ownerCoherent_variant pid .sendKeepalive) ?_
    intro _
    refine ensures_bind _ _ (purgeStagedPackets_spec_ownerCoherent_variant pid) ?_
    intro _
    refine ensures_bind _ _ hread ?_
    intro p
    refine ensures_bind _ _ (hambient (AmbientM.branch .retransmitZeroKeyNotPending
      !(p.timerPending .zeroKeyMaterial))) ?_
    intro pending
    cases pending with
    | false => exact hpure ()
    | true =>
      exact ensures_bind _ _ (modPeerTimer_spec_ownerCoherent_variant
        .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS)
        (fun _ => hpure ())
  change Ensures (expiredRetransmitHandshake pid) safe (fun _ => safe)
  rw [TimerDiscipline.expiredRetransmit_source]
  refine ensures_bind _ _ hread ?_
  intro p
  refine ensures_bind _ _ (hambient (AmbientM.branchCmp .retransmitGiveUp
    (p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) p.timerHandshakeAttempts MAX_TIMER_HANDSHAKES)) ?_
  intro giveup
  cases giveup with
  | true => exact giveUp
  | false =>
    have queued : Ensures (sendQueuedHandshakeInitiation pid true) safe (fun _ => safe) :=
      sendQueuedHandshakeInitiation_owner_coherent pid true
    have retry : Ensures (do
        (do let p ← getPeer pid; setPeer pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
        clearPeerEndpointSrc pid
        sendQueuedHandshakeInitiation pid true) safe (fun _ => safe) :=
      ensures_bind _ _ increment (fun _ => ensures_bind _ _
        (clearPeerEndpointSrc_spec_ownerCoherent_variant pid) (fun _ => queued))
    simpa only [Bool.false_eq_true,ite_false,bind_assoc] using retry


end Leanux.Proofs.WG.Index
