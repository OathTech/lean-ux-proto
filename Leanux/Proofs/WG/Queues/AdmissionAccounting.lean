import Leanux.Proofs.WG.Queues.SyscallFate
import Leanux.Proofs.WG.Queues.RemovalIdentity

/-! The final funded account makes the pending and completed-removal outcomes
exclusive. Packet identity is recovered from the actual capture stamp; a
release is never inferred merely from absence in the final store. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem removed_released (removed : AdmissionRelease.Removed c after history) :
    RxHistory.Released history (CarrierIdentity.stamp c.packet) := by
  obtain ⟨pre,post,n,skb,stamp,_,identity,certificate⟩ := removed
  simpa only [identity] using RemovalIdentity.certificate_release certificate

theorem removed_absent (removed : AdmissionRelease.Removed c after history)
    (entry : HolderEntry.Inv cs loans history w) : c.packet∉cs.map Carrier.packet := by
  obtain ⟨pre,post,n,skb,stamp,_,identity,certificate⟩ := removed
  simpa only [identity] using RemovalIdentity.certificate_absent certificate entry

theorem pending_once (entry : HolderEntry.Inv cs loans history w) (member : c∈cs) :
    (cs.map Carrier.packet).count c.packet=1 := by
  obtain ⟨holders,funded,_⟩ := entry.1.1.1
  exact funded.carriers.inventory.distinct.count_of_mem (List.mem_map.mpr ⟨c,member,rfl⟩)

/-- The accepted source occurrence keeps its strict history cut. Its packet
occurs exactly once in the residual ledger, or has an actual completed poll
disposition/release and is absent from that ledger. -/
theorem partition (fate : AdmissionRelease.Fate c final base history)
    (entry : HolderEntry.Inv final loans history finalWorld) :
    ∃ msg src cs admitted w v before after lead suffix,
      before=base++lead ∧ AdmissionCaller.Step cs admitted msg src w v before after ∧
      ReceiveEffects.Accepted cs admitted msg src w.wg v.wg w.ambient v.ambient c ∧
      history=after++suffix ∧
      ((c∈final ∧ (final.map Carrier.packet).count c.packet=1 ∧
          ¬AdmissionRelease.Removed c after history) ∨
        (c.packet∉final.map Carrier.packet ∧ AdmissionRelease.Removed c after history ∧
          RxHistory.Released history (CarrierIdentity.stamp c.packet))) := by
  obtain ⟨msg,src,cs,admitted,w,v,before,after,lead,suffix,start,step,accepted,finish,outcome⟩ := fate
  refine ⟨msg,src,cs,admitted,w,v,before,after,lead,suffix,start,step,accepted,finish,?_⟩
  rcases outcome with pending | removed
  · refine Or.inl ⟨pending,pending_once entry pending,?_⟩
    intro removed
    exact removed_absent removed entry (List.mem_map.mpr ⟨c,pending,rfl⟩)
  · exact Or.inr ⟨removed_absent removed entry,removed,removed_released removed⟩

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionAccounting
