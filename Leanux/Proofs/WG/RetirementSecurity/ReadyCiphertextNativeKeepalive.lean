import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeMaintenance

/-! Keepalive preparation edits staged plaintext only; its actual staged-send
continuation derives fresh batches whose heads remain unready from the native nonce loop. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits

theorem keepalive (pid : PeerId) : Preserves (Coherent locals active) (sendKeepalive pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have physical := (hoare_iff_run_ambient _ _ _).mp (OccurrenceHandshake.keepalive pid)
    w a result v b before.1 run
  refine ⟨physical,?_⟩
  cases result
  rw [OccurrenceHandshake.keepalive_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,prepared,tail⟩ := run
  have kept := (hoare_iff_run_ambient _ _ _).mp
    (ready_frame (OccurrenceHandshake.keepalive_prepare_geometry pid)
      (OccurrenceHandshake.keepalive_prepare_queues pid))
    w a ready u c ⟨⟨before.1.1.bounded,before.1.2.1⟩,before.2⟩ prepared
  cases ready with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact kept.2
  | true => exact send kept pid c b tail

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Native
