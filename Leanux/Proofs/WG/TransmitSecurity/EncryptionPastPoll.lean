import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastWorker

/-! A native encryption-ring poll moves a live alias into the active list.
Logical pending identities are conserved despite stale physical ring cells. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

/-- Poll transfers, rather than copies, the selected live batch. Historical
encryption identities remain excluded from both ring and active aliases. -/
theorem poll (physical : TxDisposition.LiveFrontier.Physical w)
    (before : Inv past active (view w)) (a b : Ambient)
    (run : (TxRing.pollSource.run w).run a = .ok ((out,v),b)) :
    Inv past (out.toList ++ active) (view v) := by
  cases device : w.dev with
  | none => simp [TxRing.pollSource,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    obtain ⟨n,h,refines⟩ := physical d device
    have cell : TxRing.nativeCell w = some (d.ifindex,d.encryptQueue) := by simp [TxRing.nativeCell,device]
    obtain ⟨selected,_⟩ := TxRing.poll_result cell run
    have old := refines.initialized.2.1
    have next := (refines.step .poll).initialized.2.1
    simp only [Ring.Journal.step,Ring.Journal.admitted,Ring.Journal.consumed,
      List.filterMap_append,List.filterMap_cons,List.filterMap_nil,List.append_nil] at next
    change Ring.Journal.admitted h = (Ring.Journal.consumed h ++ d.encryptQueue.consume.1.toList) ++
      d.encryptQueue.consume.2.items at next
    rw [old,List.append_assoc] at next
    have sequence : d.encryptQueue.items = out.toList ++ d.encryptQueue.consume.2.items := by
      simpa only [selected] using List.append_cancel_left next
    have sameRun := run
    simp [TxRing.pollSource,getDev,device,modifyDev] at sameRun
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := sameRun
    refine ⟨before.1,?_⟩
    intro label member
    apply (before.2 label member).shrink
    · exact Nat.le_refl _
    intro current resident
    have equal : current = ⟨d.ifindex,d.nextSkb,d.encryptQueue.consume.2.items⟩ := by
      simpa only [view,device,Option.map_some,Option.some.injEq] using resident.symm
    subst current
    refine ⟨⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩,by simp [view,device],rfl,Nat.le_refl _,?_⟩
    have transfer : (d.encryptQueue.consume.2.items ++ (d.encryptQueue.consume.1.toList ++ active)).Perm
        (d.encryptQueue.items ++ active) := by
      rw [sequence]
      simpa only [List.append_assoc] using
        (show (d.encryptQueue.consume.2.items ++ d.encryptQueue.consume.1.toList).Perm
          (d.encryptQueue.consume.1.toList ++ d.encryptQueue.consume.2.items) from List.perm_append_comm).append_right active
    exact fun _ present => transfer.flatten.mem_iff.mp present

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
