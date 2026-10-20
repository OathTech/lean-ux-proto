import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeInterpretation

/-! Counted release, free and socket receipts complete on the same native
world. Their current-state partitions come from the actual successor ledger;
neither an erase nor a socket operation is repeated to recover accounting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting.Receipt
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations RetirementSecurity AllocatedObligation CompleteCarrier

theorem purge {w : World} (before : Accounted h ledger debts locals w.wg)
    (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    let target:=Timer.Points.Purge.state pid p d w .cleared
    let last:=Timer.Points.Purge.history pid p d w h .recorded
    (∃after,Current last after debts locals target.wg) ∧
      runPrefix (Timer.Points.Purge.suffix pid p d w .cleared) target h=(.ok ((),target),last) := by
  have cut:=Timer.Points.Purge.awaiting_cut before device resident
  exact ⟨⟨_,Current.of_accounted cut.2.2.2.1⟩,cut.2.2.1⟩

theorem release (before : Accounted h ledger debts locals w)
    (native : ((HandshakeSecurity.StagedDisposal.releaseCut peer).run w).run a=.ok ((value,v),b)) :
    let event:=PeerRetirement.releaseEvent peer value w v a b
    (∃after,Current (h++[event]) after debts locals v) ∧
      runWGPrefix (PeerRetirement.Points.receipt peer value w v a b) v b h=(.ok (((),v),b),h++[event]) ∧
      runWGPrefix (CausalJournal.peerRelease peer) w a h=
        runWGPrefix (PeerRetirement.remaining peer w a (pure value)) v b h := by
  obtain ⟨after,_,_,account⟩:=PeerRetirement.Points.native_account before native
  exact ⟨⟨after,Current.of_accounted account⟩,PeerRetirement.Points.receipt_total _ _ _ _ _ _ _,
    (PeerRetirement.Points.Point.erased value native).continuation⟩

theorem nested_release {w : World} (before : Accounted h ledger debts locals w.wg)
    (native : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h=(.ok ((value,v),b),middle)) :
    let target:={w with wg:=v,ambient:=b}
    let event:=PeerRelease.receipt peer value w.wg v w.ambient b
    (∃after,Current (middle++[event]) after debts locals v) ∧
      runPrefix (emitPrefix event) target middle=(.ok ((),target),middle++[event]) ∧
      runPrefix (Admission.actualOps.release peer) w h=
        runPrefix (NestedPeer.resume peer w (pure value)) target middle := by
  obtain ⟨after,_,_,account⟩:=NestedPeer.cut_accounted before native
  exact ⟨⟨after,Current.of_accounted account⟩,rfl,NestedPeer.cut_residual native⟩

theorem nested_erase {w : World} (before : Accounted h ledger debts locals w.wg)
    (checked : runWGPrefix (NestedPeer.prefixAt NestedPeer.actual .checked peer) w.wg w.ambient h=
      (.ok ((some (pid,p),v),b),middle)) :
    let target:={w with wg:=NestedPeer.erasedWorld pid p.staged.length v,ambient:=b}
    let last:=middle++NestedPeer.eraseEvents v pid++
      [PeerRelease.receipt peer (some (pid,p)) w.wg target.wg w.ambient b]
    (∃after,Current last after debts locals target.wg) ∧
      runPrefix (NestedPeer.pendingRecords peer pid p w v b) target middle=(.ok ((),target),last) ∧
      runPrefix (Admission.actualOps.release peer) w h=
        runPrefix (do NestedPeer.pendingRecords peer pid p w v b; PeerRelease.finish (some (pid,p))) target middle := by
  obtain ⟨after,_,_,account⟩:=NestedPeer.cut_accounted before (NestedPeer.erased_cut checked)
  exact ⟨⟨after,Current.of_accounted account⟩,NestedPeer.records_run _ _ _ _ _ _ _,
    NestedPeer.erased_records_residual checked⟩

theorem create_free (cut : CreatePoints.FreeCut reason pid skb remaining h ledger debts locals w)
    (phase : CleanupPrimitive.Phase) :
    Current (CleanupPrimitive.finished reason skb w cut.after h) cut.next debts
      (⟨.unpublished,pid,remaining⟩::locals) cut.after.wg ∧
      runPrefix (CleanupPrimitive.due phase reason skb w cut.after) cut.after
        (CleanupPrimitive.current phase w skb h)=
        (.ok ((),cut.after),CleanupPrimitive.finished reason skb w cut.after h) :=
  ⟨Current.of_accounted cut.accounted,CleanupPrimitive.due_run phase reason skb w cut.after h⟩

theorem dead_free
    (waiting : CleanupPrimitive.Awaiting phase reason pid debts locals skb remaining w h ledger v after) :
    Current (CleanupPrimitive.finished reason skb w v h) after debts (⟨.selected,pid,remaining⟩::locals) v.wg ∧
      runPrefix (CleanupPrimitive.due phase reason skb w v) v (CleanupPrimitive.current phase w skb h)=
        (.ok ((),v),CleanupPrimitive.finished reason skb w v h) :=
  ⟨Current.of_accounted waiting.linearized.2.2.2.2.1,waiting.linearized.2.2.2.1⟩

theorem socket
    (waiting : SocketInterior.Awaiting context skb rest packet peer ipv4 h ledger debts entry result frontWorld events) :
    let target:=SocketInterior.resultWorld frontWorld result
    let event:=Event.old (.socket (SocketInterior.receipt context.pid skb packet peer ipv4 entry result frontWorld))
    Stable (waiting.prior++[event]) target.wg ∧
      runPrefix (do emitPrefix event; pure (SocketInterior.resultCode result)) target waiting.prior=
        (.ok (SocketInterior.resultCode result,target),waiting.prior++[event]) :=
  ⟨Stable.of_accounted ⟨waiting.after.entry,waiting.afterComplete⟩,waiting.receipt_total⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting.Receipt
