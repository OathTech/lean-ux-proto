import Leanux.Proofs.WG.HandshakeSecurity.ReceiptClaims

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem timestamp_survives_consumption_stop (pid : PeerId) (old t : List UInt8)
    (w v : WGWorld) (a b : Ambient) (h : List TimestampReceipt) (stop : Stop)
    (newer : memcmp t old = .gt)
    (written : ((writeTimestamp pid t).run w).run
      (CounterWindow.record a .consumeNewerTimestamp true) = .ok (((), v), b))
    (stopped : ((hiddenClock64 .consumptionNow : WG.M Int64).run v).run b = .error stop) :
    runWGPrefix (do
      timestampObserved pid old t
      liftWGPrefix (hiddenClock64 .consumptionNow : WG.M Int64)) w a h =
      (.error stop, h ++ [⟨pid, old, t, ⟨(), w, v,
        CounterWindow.record a .consumeNewerTimestamp true, b⟩⟩]) := by
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have he := timestamp_run pid old t w a h
  simp only [newer, beq_self_eq_true, ite_true, written] at he
  rw [show runStatePrefix (timestampObserved pid old t) w a h = _ from he]
  exact congrArg (fun result => (result, h ++ [⟨pid, old, t, ⟨(), w, v,
    CounterWindow.record a .consumeNewerTimestamp true, b⟩⟩])) stopped

end Leanux.Proofs.WG.HandshakeSecurity
