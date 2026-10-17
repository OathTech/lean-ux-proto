import Leanux.Proofs.WG.Queues.HolderEncryptFrames
import Leanux.Proofs.Framing.WGDeviceLifecycle

/-! Guarded device creation cannot discard an outstanding funded account.
An absent entry forces that account empty; successful newlink establishes the
new device's empty inventory and initialized receive ring from its source. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceCreate
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private def fromStore (s : WGStoreView) : WGWorld :=
  {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}

private theorem link_fields (w : WGWorld) :
    HolderEncrypt.fields (fromStore (linkView w))=HolderEncrypt.fields w := by
  unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  cases hd:w.dev <;> simp [fromStore,linkView,linkStore,wgStoreView,linkDevice,hd,rxView]

theorem link_boundary (hi : Boundary cs loans w) (same : linkView v=linkView w) : Boundary cs loans v := by
  apply HolderEncrypt.boundary_fields hi
  rw [←link_fields v,←link_fields w,same]

/-- No ledger entry, loan or dump cursor can survive an absent device in the
complete funded account. This follows from inventory and charged residency. -/
theorem absent (hi : Boundary cs loans w) (none : w.dev=Option.none) :
    cs=[] ∧ loans=[] ∧ activeCursor w.nlSock7=Option.none ∧ activeCursor w.nlSock8=Option.none := by
  obtain ⟨holders,funded,_⟩ := hi
  have packets : cs=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro c member
    obtain ⟨_,p,stored,_⟩ := funded.carriers.inventory.present c member
    simp [packetAt,none] at stored
  have reservations : holders.owners ++ loans=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro o member
    have positive := List.count_pos_iff.mpr member
    have balance := funded.carriers.funded o
    simp [RxCredits.balance,resident,none] at balance
    unfold demand at balance
    omega
  obtain ⟨owners,loansEmpty⟩ := List.append_eq_nil_iff.mp reservations
  refine ⟨packets,loansEmpty,?_,?_⟩
  · rw [←funded.aligned.cursor7]
    cases cursor:holders.cursor7 with
    | none => rfl
    | some o =>
      have member : o ∈ holders.owners := by simp [DurableHolders.owners,cursor]
      rw [owners] at member
      cases member
  · rw [←funded.aligned.cursor8]
    cases cursor:holders.cursor8 with
    | none => rfl
    | some o =>
      have member : o ∈ holders.owners := by simp [DurableHolders.owners,cursor]
      rw [owners] at member
      cases member

private def Empty (w : WGWorld) : Prop := ∀ d, w.dev=some d →
  d.peers={} ∧ d.rxSkbs={} ∧ d.peerList=[] ∧ d.sendWorkQueue=[] ∧ d.clearWorkQueue=[] ∧
  d.decryptQueue=PtrRing.init MAX_QUEUED_PACKETS

private theorem empty_boundary (shape : Empty w)
    (cursor7 : activeCursor w.nlSock7=none) (cursor8 : activeCursor w.nlSock8=none) : Boundary [] [] w := by
  have queues : ∀ (d : Device) (pid : PeerId) (p : Peer), w.dev=some d → d.peers[pid]?=some p → p.rxQueue.all=[] := by
    intro d pid p hd hp
    simp [(shape d hd).1] at hp
  refine ⟨{},⟨?_,?_⟩,?_⟩
  · constructor
    · cases hd:w.dev with
      | none => simp
      | some d => simpa [hd] using (shape d hd).2.2.1.symm
    · intro d hd
      exact (shape d hd).2.2.2.1
    · cases hd:w.dev with
      | none => simp
      | some d => simpa [hd] using (shape d hd).2.2.2.2.1.symm
    · intro pid batches found
      cases hd:w.dev with
      | none => simp [handoffTxView,hd] at found
      | some d => simp [handoffTxView,hd,(shape d hd).1] at found
    · exact cursor7.symm
    · exact cursor8.symm
  · change CarrierState [] [] w
    apply empty_carriers w
    · intro d id hd; simp [(shape d hd).2.1]
    · exact queues
    · intro pid target peer kid htarget hpeer
      simp [(shape target htarget).1] at hpeer
  · apply empty_stable w
    · intro d hd
      rw [(shape d hd).2.2.2.2.2]
      exact (pinned_const _private.Leanux.Proofs.WG.Queues.RxCarrierInitial.«0».Leanux.Proofs.WG.Queues.RxCredits.initialRing_items) _
    · exact queues

private theorem fresh_empty (same : linkView v=registeredLink (setupLink (linkView w))) : Empty v := by
  intro d hd
  have fields := congrArg (fun s : WGStoreView => s.dev.map fun d =>
    (d.peers,d.rxSkbs,d.peerList,d.sendWorkQueue,d.clearWorkQueue,d.decryptQueue)) same
  simpa only [linkView,linkStore,wgStoreView,registeredLink,setupLink,linkDevice,
    hd,Option.map_some,Option.some.injEq,Prod.mk.injEq] using fields

/-- Complete actual guarded creation, including errno returns, preserves the
same logical ledger. A newly created device starts with no outstanding charge. -/
theorem create : Preserves (Boundary cs loans) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨none,fresh⟩
  · exact link_boundary hi same
  · have absentDev : w.dev=Option.none := by
      simpa [linkView,linkStore,wgStoreView] using none
    obtain ⟨packets,loansEmpty,cursor7,cursor8⟩ := absent hi absentDev
    subst cs
    subst loans
    apply empty_boundary (fresh_empty fresh)
    · have sock : v.nlSock7=w.nlSock7 := congrArg WGStoreView.nlSock7 fresh
      exact sock ▸ cursor7
    · have sock : v.nlSock8=w.nlSock8 := congrArg WGStoreView.nlSock8 fresh
      exact sock ▸ cursor8

/-- Absence has no ring; a present device carries an actual initialized-ring journal. -/
def OptionalPhysical (w : WGWorld) : Prop :=
  w.dev=none ∨ ∃ epoch n history, NativeRxInv epoch (PtrRing.init n) history w

theorem physical_initial (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w=wgStoreView (Runner.initialWG net bare)) : OptionalPhysical w := by
  rcases ring_initial net bare w same with none | ring
  · exact Or.inl none
  · exact Or.inr ⟨3,MAX_QUEUED_PACKETS,[],ring⟩

/-- A successful new device obtains its own empty physical-ring history;
normal refusal retains the old one. No absent ring is fabricated. -/
theorem create_physical : Preserves OptionalPhysical wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have cells : RxRing.nativeCell v=RxRing.nativeCell w := by
      have eq := congrArg (fun s : WGStoreView => s.dev.map fun d => (d.ifindex,d.decryptQueue)) same
      simpa only [RxRing.nativeCell,linkView,linkStore,wgStoreView,linkDevice,
        Option.map_map,Function.comp_def] using eq
    rcases hi with none | ⟨epoch,n,history,ring,refines,cell⟩
    · left
      simpa [RxRing.nativeCell,none] using cells
    · exact Or.inr ⟨epoch,n,history,ring,refines,cells.trans cell⟩
  · right
    refine ⟨w.netIfindexNext,MAX_QUEUED_PACKETS,[],PtrRing.init MAX_QUEUED_PACKETS,⟨[],rfl⟩,?_⟩
    have cells := congrArg (fun s : WGStoreView => s.dev.map fun d => (d.ifindex,d.decryptQueue)) fresh
    simpa only [RxRing.nativeCell,linkView,linkStore,wgStoreView,registeredLink,setupLink,linkDevice,
      Option.map_map,Option.map_some,Function.comp_def] using cells

end Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceCreate
