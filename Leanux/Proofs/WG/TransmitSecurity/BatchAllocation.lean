import Leanux.Proofs.WG.TransmitSecurity.BatchHistory

/-! The observed native allocator retains the source batch's peer and key. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchHistory
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxHeartbeats 400000

theorem reserve (slot : KeypairId) : StatePrefixPreserves (Keep (fun _ => P)) Safe (Journal.reserve slot) := by
  apply quiet ((StateAppends.focus _ _ _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved
      (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved slot).run w)) _ (fun _ => rfl))
  exact fun _ _ _ before => before

theorem allocate (pid : PeerId) (slot : KeypairId) (packets : List DataPacket) :
    StatePrefixEnsures (Keep (fun _ => Aligned pid slot packets)) Safe (Journal.allocate packets)
      (fun _ h _ _ => Safe h) := by
  intro w a h hi
  unfold Journal.allocate
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb))
    (Journal.Event.allocated packets) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((packets.mapM newTxSkb).run w).run a with
  | error stop => exact ⟨[],by simp,hi.1,True.intro⟩
  | ok out =>
    obtain ⟨⟨items,v⟩,b⟩ := out
    let r : WGRunWitness (List SkbId) := ⟨items,w,v,a,b⟩
    have safe : Safe (h ++ [.allocated packets r]) := by
      apply hi.1.append
      intro pre event post position
      cases pre with
      | nil =>
        simp only [List.nil_append,List.cons.injEq] at position
        obtain ⟨same,_⟩ := position
        subst event
        exact ⟨run,pid,slot,hi.2⟩
      | cons e es =>
        have sizes := congrArg List.length position
        simp only [List.length_append,List.length_cons,List.length_nil] at sizes
        omega
    exact ⟨[.allocated packets r],rfl,safe,safe⟩

end Leanux.Proofs.WG.TransmitSecurity.BatchHistory
