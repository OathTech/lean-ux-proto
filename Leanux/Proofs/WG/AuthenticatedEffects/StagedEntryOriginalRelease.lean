import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryOriginalReleaseFrames

/-! Original (non-nested) peer-release source transport. The actual native
counted cut updates one fixed ledger before its suffix can fail. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.OriginalRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation Staged.Obligations CausalJournal
open HandshakeSecurity.StagedDisposal

theorem native_entry (peer : Option PeerId) (before : Inv history ledger debts locals w)
    (a b : Ambient) (native : ((releaseCut peer).run w).run a = .ok ((value,v),b)) :
    ∃ after, Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
      PeerRelease.Successor value w history.length ledger after ∧
      Inv (history ++ [.stagedDisposal (.release peer ⟨value,w,v,a,b⟩)]) after debts locals v := by
  obtain ⟨covered,unique,bounds⟩ := PeerRelease.cut_ownership peer before.coverage before.inventory before.packets a b native
  cases value with
  | none => exact ⟨ledger,Staged.Obligations.Step.refl _,AllocatedFrame.refl _,rfl,
      CompletionBatch.release_none_entry peer ⟨none,w,v,a,b⟩ native rfl before bounds covered unique⟩
  | some pair =>
    obtain ⟨pid,p⟩ := pair
    obtain ⟨generation,epoch,step,frame,entry,_,_⟩ :=
      CompletionBatch.release_final_entry peer ⟨some (pid,p),w,v,a,b⟩ native rfl before bounds covered unique
    exact ⟨_,step,frame,⟨generation,epoch,rfl⟩,entry⟩

/-- The actual release retains complete accounting on every path, including
its reached counted cut if the later timer/retirement suffix stops. -/
theorem checked (peer : Option PeerId) (Safe : List CausalJournal.Event → Prop)
    (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h) :
    StatePrefixEnsures (fun h w _ => Inv h ledger debts locals w) Safe
      (CausalJournal.peerRelease peer)
      (fun _ h w _ => ∃ after, Inv h after debts locals w) := by
  intro w a h before
  have equation := StagedAdmission.Front.put_run peer w a h
  change runPrefix ((CausalJournal.peerRelease peer).run w) a h = _ at equation
  rw [equation]
  cases native : ((releaseCut peer).run w).run a with
  | error stop => exact ⟨[],by simp,entrySafe _ _ _ before,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    obtain ⟨after,_,_,_,entry⟩ := native_entry peer before a b native
    cases value with
    | none => exact ⟨[.stagedDisposal (.release peer ⟨none,w,v,a,b⟩)],rfl,
        entrySafe _ _ _ entry,after,entry⟩
    | some pair =>
      obtain ⟨pid,p⟩ := pair
      refine ⟨[.stagedDisposal (.release peer ⟨some (pid,p),w,v,a,b⟩)],rfl,entrySafe _ _ _ entry,?_⟩
      dsimp only
      cases performed : ((releaseFinish pid p).run v).run b with
      | error stop => trivial
      | ok out =>
        obtain ⟨⟨ignored,u⟩,c⟩ := out
        exact ⟨after,(hoare_iff_run_ambient _ _ _).mp (finish pid p) v b ignored u c entry performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.OriginalRelease
