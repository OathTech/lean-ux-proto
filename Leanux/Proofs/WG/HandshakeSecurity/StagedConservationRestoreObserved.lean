import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationRestoreCore
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration

/-! Actual native restoration receipts, independent of initialized historical
material invariants and therefore usable by the common source observer. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

structure Receipt where
  pid : PeerId
  packets : List Packet
  run : WGRunWitness Unit

def Receipt.Valid (r : Receipt) : Prop := r.run.Valid (nativeRestore r.pid r.packets)

def observed (record : Receipt → E) (pid : PeerId) (packets : List Packet) : WGPrefix E Unit :=
  receiptWGObserved (liftWGPrefix (nativeRestore pid packets)) (fun run => record ⟨pid,packets,run⟩)


theorem observed_erases (record : Receipt → E) (pid : PeerId) (packets : List Packet) :
    ErasesStatePrefix (observed record pid packets) (nativeRestore pid packets) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem observed_projects (record : Receipt → E) (ρ : E → Option F)
    (quiet : ∀ r, ρ (record r) = none) (pid : PeerId) (packets : List Packet) :
    StateProjectsPrefix ρ id (observed record pid packets)
      (liftWGPrefix (nativeRestore pid packets)) :=
  Exchange.receipt_ignored ρ _ _ _
    (Exchange.quiet_native_projection ρ _ _ (erasesStatePrefix_lift _) (fun _ _ _ => rfl))
    (fun _ => quiet _)

theorem observed_completed (record : Receipt → E) (pid : PeerId) (packets : List Packet)
    (w v : WGWorld) (a b : Ambient) (h : List E)
    (run : ((nativeRestore pid packets).run w).run a = .ok (((),v),b)) :
    runWGPrefix (observed record pid packets) w a h =
      (.ok (((),v),b),h ++ [record ⟨pid,packets,⟨(),w,v,a,b⟩⟩]) := by
  rw [observed,runWGPrefix_receiptWGObserved,runWGPrefix_lift,run]


end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
