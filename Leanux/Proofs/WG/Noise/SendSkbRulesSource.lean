import Leanux.Proofs.WG.Noise.DataCompletionRulesSource
import Leanux.Proofs.WG.Noise.SlotFrames
import Leanux.Proofs.WG.Queues.TxFreshReservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DataCompletionRules
open Leanux Leanux.WG Lifetimes Queues Leanux.Proofs.Framing Std.Do

/-- One predicate-parametric traversal of the actual socket send and successful
byte-accounting path, including its actual endpoint-family guards. -/
theorem sendSkb_preserves (P : WGWorld → Prop) (pid : PeerId) (bytes : List UInt8) (ds : Nat)
    (v4 : ∀ e exactRx, Preserves P (send4 e (some pid) bytes ds exactRx))
    (v6 : ∀ e exactRx, Preserves P (send6 e (some pid) bytes ds exactRx))
    (update : Preserves P (modifyPeer pid (fun p => {p with txBytes:=p.txBytes+bytes.length}))) :
    Preserves P (sendSkbToPeer pid bytes ds) := by
  have count (ret : Bool) : Preserves P (do
      let p ← getPeer pid
      setPeer pid {p with txBytes:=p.txBytes+bytes.length}
      pure ret) := by
    change Preserves P (do let p ← getPeer pid; setPeer pid {p with txBytes:=p.txBytes+bytes.length}) at update
    simpa only [bind_assoc] using preserves_bind update
      (fun _ => (preserves_pure ret : Preserves P (pure ret : WG.M Bool)))
  have read : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b pre run
    exact (getPeer_normal pid w v p a b run).1 ▸ pre
  unfold sendSkbToPeer
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | env_operation_fact count
    | (rx_retention_head getPeer; exact read)
    | (rx_retention_head send4; exact v4 _ _)
    | (rx_retention_head send6; exact v6 _ _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step
end Leanux.Proofs.WG.Noise.DataCompletionRules
