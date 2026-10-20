import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSkbAccessSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadGetterFrames

/-! Allocation points expose the device getter, isolated packet-store
computation and adapter write-back inside each actual mapM iteration. The
single batch receipt stays outside these native points. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity CausalJournal

inductive CellPoint (packet : DataPacket) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | reading (point : ReadGetter.Point ReadGetter.device w a v b) : CellPoint packet w a v b
  | component (device : w.dev=some d)
      (performed : ((SkbStore.newTx packet).run (SkbAccess.input d)).run a=.ok ((value,store),b)) :
      CellPoint packet w a w b
  | returned (performed : ((newTxSkb packet).run w).run a=.ok ((value,v),b)) : CellPoint packet w a v b

theorem CellPoint.remaining (point : CellPoint packet w a v b) :
    ∃ rest : WG.M SkbId,((newTxSkb packet).run w).run a=(rest.run v).run b := by
  cases point with
  | reading point =>
      obtain ⟨rest,same⟩ := point.remaining
      exact ⟨rest >>= SkbAccess.afterRead (SkbStore.newTx packet),by
        change ((liftSkb (SkbStore.newTx packet)).run w).run a=_
        rw [SkbAccess.source]
        simp only [StateT.run_bind,same]⟩
  | component device performed => exact (SkbAccess.Point.component device performed).remaining
  | returned performed => exact ⟨pure _,performed⟩

inductive Point : List DataPacket → WGWorld → Ambient → WGWorld → Ambient → Prop where
  | entry : Point packets w a w a
  | head (point : CellPoint packet w a v b) : Point (packet::packets) w a v b
  | tail (first : ((newTxSkb packet).run w).run a=.ok ((skb,u),a))
      (point : Point packets u a v b) : Point (packet::packets) w a v b

theorem Point.remaining (point : Point packets w a v b) :
    ∃ rest : WG.M (List SkbId),((packets.mapM newTxSkb).run w).run a=(rest.run v).run b := by
  induction point with
  | entry => exact ⟨_,rfl⟩
  | @head packet w a v b packets point =>
      obtain ⟨rest,same⟩ := point.remaining
      exact ⟨do let skb←rest;let items←packets.mapM newTxSkb;pure (skb::items),by
        simp only [List.mapM_cons,StateT.run_bind,same]⟩
  | @tail packet w a skb u packets v b first point ih =>
      obtain ⟨rest,same⟩ := ih
      exact ⟨do let items←rest;pure (skb::items),by
        simp [List.mapM_cons,StateT.run_bind,first,same]⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
