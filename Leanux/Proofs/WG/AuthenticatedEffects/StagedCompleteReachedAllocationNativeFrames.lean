import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationNativeSource

/-! Every adapter point has the physical state of an actual allocation
cursor. Before write-back the isolated component has not installed a cell;
after write-back exactly that one native allocation extends the prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal

theorem newTx_clock (performed : ((newTxSkb packet).run w).run a=.ok ((value,v),b)) : b=a := by
  cases device : w.dev with
  | none => simp [newTxSkb,liftSkb_run,device] at performed
  | some d => rw [Packets.newTxSkb_run w a d packet device] at performed;cases performed;rfl

theorem CellPoint.path (point : CellPoint packet w a v b) (packets : List DataPacket) :
    ∃ count items,b=a ∧ Path (packet::packets) w a count items v := by
  cases point with
  | reading point => obtain ⟨rfl,rfl⟩ := point.state;exact ⟨0,[],rfl,.zero⟩
  | component device performed => cases performed;exact ⟨0,[],rfl,.zero⟩
  | returned performed =>
      obtain rfl := newTx_clock performed
      exact ⟨1,[_],rfl,.step performed .zero⟩

theorem Point.path (point : Point packets w a v b) :
    ∃ count items,b=a ∧ Path packets w a count items v := by
  induction point with
  | entry => exact ⟨0,[],rfl,.zero⟩
  | head point => exact point.path _
  | tail first point ih =>
      obtain ⟨count,items,rfl,path⟩ := ih
      exact ⟨count+1,_::items,rfl,.step first path⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Allocation
