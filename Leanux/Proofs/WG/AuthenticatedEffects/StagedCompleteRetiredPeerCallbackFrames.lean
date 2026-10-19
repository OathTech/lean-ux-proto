import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerCreationFrames

/-! Actual receive and stack callbacks produce one exact C1 handoff delta.
The upper bound follows that same delta, rather than a separately chosen
post-state holder list. These are normal-return source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders
variable {holders : DurableHolders} {carriers : RxCredits.Ledger}
  {loans : Reservations} {w v : WGWorld}

theorem Account.consume {c : RxCredits.Carrier} (account : Account holders carriers loans w)
    (stored : packetAt w c.packet = some pkt) (guard : pkt.peer = pid)
    (a b : Ambient)
    (run : ((consumeDataDone pid pkt ep).run w).run a = .ok ((result,v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ Account (holders.absorb delta) carriers loans v := by
  obtain ⟨delta,step,funded,stable⟩ := DurableHolders.consume_normal
    account.funded account.stable stored guard a b run
  have upper : Upper holders carriers (loans ++ []) w := by simpa using account.upper
  exact ⟨delta,step,funded,by simpa using upper.handoff step,stable⟩

theorem Account.stack {w v : World} (account : Account holders carriers loans w.wg)
    (packets : List (List UInt8))
    (run : (packets.forM Leanux.Env.deliverInner).run w = .ok ((),v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      Account (holders.absorb delta) carriers loans v.wg := by
  obtain ⟨delta,step,funded,stable⟩ := DurableHolders.stack_normal
    packets account.funded account.stable run
  have upper : Upper holders carriers (loans ++ []) w.wg := by simpa using account.upper
  exact ⟨delta,step,funded,by simpa using upper.handoff step,stable⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
