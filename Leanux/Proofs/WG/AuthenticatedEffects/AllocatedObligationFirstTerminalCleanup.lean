import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalSource

/-! Ordinary completion cleanup uses the existing lifetime-access observer,
not a branch-labelled terminal-drop receipt. This module retains the first
terminal while transporting the exact native free and its actual suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

/-- This is precisely the per-cell access in the final completion dispose
callback. No additional terminal event is inserted at cleanup. -/
abbrev cleanupFree (skb : SkbId) : PrefixM CausalJournal.Event Unit :=
  (HandshakeSecurity.StagedDisposal.TxSource.observed CausalJournal.txEvent
    CausalJournal.txEvent? CausalJournal.Event.stagedDisposal).access (freeTxSkbPrefix skb)

theorem cleanupFree_erases (skb : SkbId) :
    ErasesPrefix (cleanupFree skb) (liftWG (freeTxSkb skb)) :=
  focusPrefix_erases CausalJournal.txEvent CausalJournal.txEvent?
    (TxDisposition.nativeAccess_erases (freeTxSkbPrefix_erases skb))

/-- The original free has an exact erase frame independently of any terminal
reason. All other cells and the device epoch survive this atomic mutation. -/
theorem cleanup_views (skb : SkbId) (w v : World)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    Packets.epoch v.wg = Packets.epoch w.wg ∧
      PacketMaterial.view v.wg skb = none ∧
      ∀ id, id ≠ skb → PacketMaterial.view v.wg id = PacketMaterial.view w.wg id := by
  obtain ⟨device,packet,atDevice,_,after⟩ := Terminal.native_free skb w v native
  rw [after]
  refine ⟨?_,?_,?_⟩
  · simp [Packets.epoch,Packets.update,atDevice]
  · simp [PacketMaterial.view,TxDisposition.txPackets,Packets.update,atDevice]
  · intro id different
    simp [PacketMaterial.view,TxDisposition.txPackets,Packets.update,atDevice,
      Std.TreeMap.getElem?_erase,Ne.symm different]

theorem cleanup_resident (skb : SkbId) (w v : World)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v))
    (resident : Resident history ledger w.wg) (unused : Unused history ledger w.wg skb) :
    Resident history ledger v.wg := by
  obtain ⟨epoch,_,other⟩ := cleanup_views skb w v native
  intro ticket position ordinal member
  obtain ⟨generation,id,value,origin,time,cell⟩ := resident ticket position ordinal member
  have different : id ≠ skb := by
    intro same
    subst id
    exact unused ticket position ordinal member generation value origin time
  exact ⟨generation,id,value,origin,epoch.trans time,(other id different).trans cell⟩

/-- Actual ordinary cleanup preserves any prior terminal outcome and the
same fixed-ticket ledger. The observer's real suffix is retained; no synthetic
terminal-drop event or terminal reason is needed. No pending alias is assumed
away: the explicit unused-cell premise must be supplied by the entry carrier. -/
theorem cleanup_source (skb : SkbId) (w v : World)
    (history suffix : List CausalJournal.Event)
    (performed : runPrefix (cleanupFree skb) w history = (.ok ((),v),history ++ suffix))
    (valid : Valid births ledger) (resident : Resident history ledger w.wg)
    (injective : Injective history ledger)
    (terminal : (ticket,Status.terminal outcome) ∈ ledger)
    (unused : Unused history ledger w.wg skb) :
    Staged.Obligations.Step ledger ledger ∧ Valid births ledger ∧
      Resident (history ++ suffix) ledger v.wg ∧ Injective (history ++ suffix) ledger ∧
      (ticket,Status.terminal outcome) ∈ ledger ∧ PacketMaterial.view v.wg skb = none := by
  have native := (cleanupFree_erases skb w history).symm.trans (congrArg Prod.fst performed)
  have after := cleanup_resident skb w v native resident unused
  exact ⟨.refl ledger,valid,after.append suffix,injective.append after suffix,
    terminal,(cleanup_views skb w v native).2.1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
