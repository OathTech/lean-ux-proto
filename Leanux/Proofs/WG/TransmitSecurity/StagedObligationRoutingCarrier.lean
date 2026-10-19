import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionNative

/-! The successful routing receipt appends its canonical new tickets to the
same incoming ledger at the actual splice entry. Earlier overflow/release
steps must already have been transported to that entry by the front source. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins Queues
open AuthenticatedEffects CausalJournal

/-- Actual routing and splice add exactly this receipt's packet occurrences.
Existing terminals, allocated cells and cleanup debts retain their identity;
the preceding native front subcuts remain explicit until composition. -/
theorem core_routed (r : Journal.RoutingHistory.Receipt) (pid : PeerId)
    (selected : r.run.value = .ok pid) (u q w : WGWorld) (a b c : Ambient)
    (check : ((Packets.txCheck r.family r.addr r.packets r.mtu).run r.run.before).run r.run.ambientBefore = .ok ((true,u),a))
    (lookup : ((lookupDst r.family r.addr).run u).run a = .ok ((some pid,q),b))
    (select : ((Packets.txSelect r.family r.packets r.mtu (some pid)).run q).run b =
      .ok ((.ok (pid,r.packets.map (fun p => {p with mtu := r.mtu})),w),c))
    (spliceRun : ((Lifetimes.xmitSplice pid (r.packets.map (fun p => {p with mtu := r.mtu}))).run w).run c =
      .ok (((),r.run.after),r.run.ambientAfter))
    (before : Core history ledger debts w) :
    ∃ generation stamp,
      let added := r.packets.map (fun p => {p with mtu := r.mtu})
      let event := Event.old (.routed r.family r.addr r.packets r.mtu r.run)
      let after := StagedAdmission.appendBirths ledger history.length (.staged generation pid stamp) added
      Core (history ++ [event]) after debts r.run.after ∧
        (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
          (ticket,Status.terminal outcome) ∈ after) ∧ dropped r.run.after = dropped w := by
  obtain ⟨generation,stamp,valid,_,queues,terminals,charged⟩ :=
    StagedAdmission.routed r pid selected u q w a b c check lookup select spliceRun
      before.valid (births_bounded history) before.queues
  let added := r.packets.map (fun p => {p with mtu := r.mtu})
  let cut : WGRunWitness Unit := ⟨(),w,r.run.after,c,r.run.ambientAfter⟩
  obtain ⟨d,_,device,_,after,_⟩ := Staged.splice pid added cut spliceRun
  dsimp only [cut] at device after
  have epoch : Packets.epoch r.run.after = Packets.epoch w := by simp [Packets.epoch,device,after]
  have cells : PacketMaterial.view r.run.after = PacketMaterial.view w := by
    funext id
    simp [PacketMaterial.view,TxDisposition.txPackets,device,after]
  refine ⟨generation,stamp,⟨?_,queues,
    (before.selected.admitted history.length generation pid stamp added).append _,
    ((before.physical.ledger_frame (admission_allocated_frame _ _ _ _ added)).views epoch cells).append _⟩,
    terminals,charged⟩
  simpa only [births_emit,birthPackets,selected] using valid

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
