import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxCompletionFrames
import Leanux.Proofs.WG.Queues.HolderPollCallbacks

/-! Poll callbacks preserve an independent stable remainder while the
selected RX cell remains charged. Each result uses the native callback's
one concrete handoff delta for both reference bounds. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Lifetimes Queues Queues.RxCredits DurableHolders

theorem Phased.consume {c : RxCredits.Carrier}
    (account : Phased holders carriers loans w) (stable : StableRx rest w)
    (stored : packetAt w c.packet = some pkt) (guard : pkt.peer = pid)
    (a b : Ambient)
    (run : ((consumeDataDone pid pkt ep).run w).run a = .ok ((result,v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧
      Phased (holders.absorb delta) carriers loans v ∧ StableRx rest v := by
  obtain ⟨delta,step,funded,boundary⟩ := DurableHolders.consume_normal
    account.funded stable stored guard a b run
  have upper : Upper holders carriers (loans ++ []) w := by simpa using account.upper
  exact ⟨delta,step,⟨funded,by simpa using upper.handoff step⟩,boundary⟩

theorem Phased.stack {w v : World}
    (account : Phased holders carriers loans w.wg) (stable : StableRx rest w.wg)
    (packets : List (List UInt8))
    (run : (packets.forM Leanux.Env.deliverInner).run w = .ok ((),v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      Phased (holders.absorb delta) carriers loans v.wg ∧ StableRx rest v.wg := by
  obtain ⟨delta,step,funded,boundary⟩ := DurableHolders.stack_normal
    packets account.funded stable run
  have upper : Upper holders carriers (loans ++ []) w.wg := by simpa using account.upper
  exact ⟨delta,step,⟨funded,by simpa using upper.handoff step⟩,boundary⟩

theorem Phased.gro_receive {w v : World}
    (account : Phased holders carriers loans w.wg) (stable : StableRx rest w.wg)
    (g : GroState) (bytes : List UInt8)
    (run : (napiGroReceive (fun xs => xs.forM Leanux.Env.deliverInner) g bytes).run w =
      .ok (result,v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      Phased (holders.absorb delta) carriers loans v.wg ∧ StableRx rest v.wg := by
  obtain ⟨delta,step,funded,boundary⟩ := DurableHolders.gro_receive_normal
    g bytes account.funded stable run
  have upper : Upper holders carriers (loans ++ []) w.wg := by simpa using account.upper
  exact ⟨delta,step,⟨funded,by simpa using upper.handoff step⟩,boundary⟩

theorem Phased.gro_flush {w v : World}
    (account : Phased holders carriers loans w.wg) (stable : StableRx rest w.wg)
    (g : GroState)
    (run : (napiGroFlushAll (fun xs => xs.forM Leanux.Env.deliverInner) g).run w = .ok ((),v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      Phased (holders.absorb delta) carriers loans v.wg ∧ StableRx rest v.wg := by
  obtain ⟨delta,step,funded,boundary⟩ := DurableHolders.gro_flush_normal
    g account.funded stable run
  have upper : Upper holders carriers (loans ++ []) w.wg := by simpa using account.upper
  exact ⟨delta,step,⟨funded,by simpa using upper.handoff step⟩,boundary⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
