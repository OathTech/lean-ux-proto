import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastCreation
import Leanux.Proofs.WG.Queues.TxLiveSend

/-! Staged-send leaf frames carry live-ring bounds beside historical exclusion.
Allocation and submission are the separate non-frame source steps. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TxDisposition

def Ready (past : List (Option Nat × SkbId)) (active : List (List SkbId)) (w : WGWorld) : Prop :=
  LiveFrontier.Ready w ∧ Inv past active (view w)

theorem ready_frame {action : WG.M α} (live : Preserves LiveFrontier.Ready action)
    (same : SameView view action) : Preserves (Ready past active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have eq := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp live w a result v b before.1 run,eq ▸ before.2⟩

theorem ready_read_key (kid : KeypairId) : Preserves (Ready past active) (getKeypair kid) := by
  apply ready_frame ?_ (read_key kid)
  repeat' live_send_step

theorem ready_set_key (kid : KeypairId) (key : Keypair) :
    Preserves (Ready past active) (setKeypair kid key) := by
  apply ready_frame
  · unfold setKeypair
    repeat' live_send_step
  · unfold setKeypair
    apply modify_fields <;> intro d <;> rfl

theorem ready_set_peer (pid : PeerId) (peer : Peer) :
    Preserves (Ready past active) (setPeer pid peer) :=
  ready_frame (LiveFrontier.ready_frame (setPeer_metadata _ _) (TxRing.setPeer_frame _ _))
    (parts (setPeer_metadata _ _) (TxRing.setPeer_frame _ _))

theorem ready_get_key (kid : Option KeypairId) : Preserves (Ready past active) (keypairGet kid) :=
  ready_frame (LiveFrontier.key_get kid) (key_get kid)

theorem ready_no_key (pid : PeerId) (packets : List Packet) (kid : Option KeypairId) (invalid : Bool) :
    Preserves (Ready past active) (stagedOutNokey pid packets kid invalid) :=
  ready_frame (LiveFrontier.no_key pid packets kid invalid) (no_key pid packets kid invalid)

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
