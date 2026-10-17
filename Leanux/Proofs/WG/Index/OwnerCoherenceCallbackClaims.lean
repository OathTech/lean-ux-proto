import Leanux.Proofs.WG.Index.OwnerCoherenceCallbackSource
import Leanux.Proofs.WG.Index.OwnerCoherenceCallbackFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceQueuedClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- The actual new-handshake callback preserves every hashed owner. Its
endpoint cache clear and both clock/queue refusal paths remain in the source. -/
theorem expiredNewHandshake_owner_coherent (pid : PeerId) :
    Campaign2.Ensures (expiredNewHandshake pid) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  let safe : WGWorld → Prop := fun g => ∀d, g.dev = some d → HashedOwnersCoherent d
  change Ensures (expiredNewHandshake pid) safe (fun _ => safe)
  unfold expiredNewHandshake
  exact ensures_bind _ _ (clearPeerEndpointSrc_spec_ownerCoherent_variant pid)
    (fun _ => sendQueuedHandshakeInitiation_owner_coherent pid false)

/-- The actual zero-key timer callback preserves owner coherence. A successful
acquisition derives the non-final compensating put; the alternate branch only
queues clear work. No obligation for running that later worker is assumed. -/
theorem expiredZeroKeyMaterial_owner_coherent (pid : PeerId) :
    Campaign2.Ensures (expiredZeroKeyMaterial pid) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  let safe : WGWorld → Prop := fun g => ∀d, g.dev = some d → HashedOwnersCoherent d
  have hpure {α : Type} (P : WGWorld → Prop) (x : α) :
      Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (P : WGWorld → Prop) (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (P : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    hambient P (AmbientM.branch site value)
  have hpeer : Ensures (getPeer pid) safe (fun _ => safe) := by
    intro g a result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid safe)
      g a result final after pre run).1
  have hdev (P : WGWorld → Prop) : Ensures getDev P (fun _ => P) := by
    intro g a result final after pre run
    cases device : g.dev with
    | none => simp [getDev,device,invariant,AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev,device] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact pre
  have enqueue : Ensures (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]})
      (OwnerPeerHeldWG pid) (fun _ => safe) := by
    intro g a result final after pre run
    obtain ⟨coherent,d,p,device,resident,held⟩ := pre
    simp [modifyDev,device] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    intro actual actualPresent
    cases actualPresent
    exact coherent d device
  change Ensures (expiredZeroKeyMaterial pid) safe (fun _ => safe)
  unfold expiredZeroKeyMaterial
  refine ensures_bind _ _ hpeer ?_
  intro p
  refine ensures_bind _ _ (hbranch _ _ _) ?_
  intro alive
  cases alive with
  | false => exact hpure safe ()
  | true =>
    refine ensures_bind _ _ (peerGet_spec_ownerHeld_variant pid) ?_
    intro _
    refine ensures_bind _ _ (hdev (OwnerPeerHeldWG pid)) ?_
    intro d
    refine ensures_bind _ _ (hambient _ (AmbientM.peekQueuedUnit .clearPeerWorker pid)) ?_
    intro peeked
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro queued
    cases queued with
    | true => exact peerPut_ownerHeld pid
    | false =>
      exact ensures_bind _ _ (hambient _ (AmbientM.recordQueued .clearPeerWorker pid))
        (fun _ => enqueue)

end Leanux.Proofs.WG.Index
