import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerWorkFrames

/-! The selected work loan is consumed by the actual final payment. The
account indices remain identical throughout the preceding native prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Std.Do
open DurableHolders
variable {holders : DurableHolders} {carriers : RxCredits.Ledger}
  {loans : Reservations} {w v : WGWorld} {a b : Ambient} {owner : Owner}

theorem Account.queued_clear (account : Account holders carriers (owner :: loans) w)
    (run : ((queuedExpiredZeroKeyMaterial owner.slot).run w).run a = .ok (((),v),b)) :
    Account holders carriers loans v := by
  unfold queuedExpiredZeroKeyMaterial at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,cleared,ac,hclear,u',keys,ak,hkeys,hpay⟩ := run
  cases u; cases u'
  exact ((account.handshake_clear hclear).keys_clear hkeys).payment hpay

theorem Account.queued_send (account : Account holders carriers (owner :: loans) w)
    (run : ((handshakeSendWorker owner.slot).run w).run a = .ok (((),v),b)) :
    Account holders carriers loans v := by
  unfold handshakeSendWorker at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,sent,middle,hsend,hpay⟩ := run
  cases u
  exact (account.send_initiation hsend).payment hpay

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
