import Leanux.Proofs.WG.Origins.OwnerCompletion
import Leanux.Proofs.WG.Origins.OwnerConfiguration

/-! Native control operations preserve receiving-owner bounds. Peer writes
may change every peer field: this invariant observes keys and RX references,
not arbitrary peer contents. Key release uses its existing checked contract. -/
namespace Leanux.Proofs.WG.OwnerControls
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits OwnerBounds

private theorem map_carrier (f : Device → Device)
    (peer : ∀ d, (f d).nextPeer = d.nextPeer)
    (frontier : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) (hi : Carrier w) :
    Carrier {w with dev := w.dev.map f} :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_map)
    f peer frontier keys rx hi

theorem modifyDevice (f : Device → Device)
    (peer : ∀ d, (f d).nextPeer = d.nextPeer)
    (frontier : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) : Preserves Carrier (modifyDev f) := by
  unfold modifyDev
  apply hoare_modify
  intro w hi
  exact map_carrier f peer frontier keys rx hi

theorem store {α : Type} (a : WG.M α) (same : SameWGStore a) : Preserves Carrier a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
    hi (congrArg WGStoreView.dev
      ((ProjectedAction.iff_run_ambient _ _ _).mp same w ambient result v finalAmbient hr))

theorem readPeer (pid : PeerId) : Preserves Carrier (getPeer pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.read_preserves) pid

theorem writePeer (pid : PeerId) (p : Peer) : Preserves Carrier (setPeer pid p) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.write_preserves) pid p

theorem index {α : Type} (a : IndexM α) : Preserves Carrier (liftIndex a) := by
  apply hoare_liftIndex
  intro w d table hi hd
  have kept := map_carrier (fun d => {d with indexTable := table})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hi
  simpa only [hd,Option.map_some] using kept

theorem aip {α : Type} (a : AipM α) : Preserves Carrier (liftAip a) := by
  apply hoare_liftAip
  intro w d table hi hd
  have kept := map_carrier (fun d => {d with peerAllowedips := table.trie, nodes := table.nodes, nextNode := table.nextNode})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hi
  simpa only [hd,Option.map_some] using kept

macro "owner_control_step" : tactic => `(tactic| first
  | (allocation_release_head getDev; exact store _ getDev_sameWGStore)
  | (allocation_release_head getPeer; exact readPeer _)
  | (allocation_release_head setPeer; exact writePeer _ _)
  | (allocation_release_head peerPut; exact OwnerConsume.peerPut_preserves _)
  | (allocation_release_head keypairPut; exact OwnerCreation.keypairPut_preserves _ _)
  | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ Carrier)
  | (allocation_release_head modifyDev
     apply modifyDevice _ ?_ ?_ ?_ ?_
     all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Carrier)
  | (allocation_release_lift_from IndexM; exact index _)
  | (allocation_release_lift_from AipM; exact aip _)
  | (allocation_release_head liftIndex; exact index _)
  | (allocation_release_head liftAip; exact aip _)
  | (allocation_release_head get
     exact hoare_consequence (hoare_get Carrier) (fun _ h => h) (fun _ _ h => h.2))
  | (allocation_release_head modify; apply hoare_modify; intro w hi; exact hi)
  | (allocation_release_head ForIn.forIn
     apply list_view_spec id Carrier
     intro x b
     change Preserves Carrier _)
  | (first | allocation_release_head throw | allocation_release_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient result v finalAmbient hi hr
     cases hr)
  | allocation_release_step)

theorem keypairsClear_preserves (pid : PeerId) : Preserves Carrier (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' owner_control_step

theorem handshakeClear_preserves (pid : PeerId) : Preserves Carrier (handshakeClear pid) := by
  unfold handshakeClear handshakeZero
  repeat' owner_control_step

theorem queuedExpiredZeroKeyMaterial_preserves (pid : PeerId) :
    Preserves Carrier (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  repeat' first
    | (allocation_release_head handshakeClear; exact handshakeClear_preserves _)
    | (allocation_release_head keypairsClear; exact keypairsClear_preserves _)
    | owner_control_step

end Leanux.Proofs.WG.OwnerControls
