import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueuedFrames

/-! Same-ledger transport at the actual queued-initiation cuts. Its paired
repayment is nonfinal; no staged disposal is silently ignored or charged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queued
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
open HandshakeSecurity.StagedDisposal

theorem decision_entry (before : Inv h ledger debts locals w) (pid : PeerId)
    (a b : Ambient) (run : ((decisionPrefix pid).run w).run a = .ok ((decision,v),b)) :
    Inv h ledger debts locals v :=
  before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp (decision_views pid) w a decision v b run)

theorem install_entry (before : Inv h ledger debts locals w) (pid : PeerId)
    (a b : Ambient) (run : ((install pid).run w).run a = .ok (((),v),b)) : Inv h ledger debts locals v :=
  before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp (install_views pid) w a () v b run)

theorem Inv.history (before : Inv h ledger debts locals w) (suffix : List CausalJournal.Event)
    (quiet : ∀ event ∈ suffix, birthPackets event = []) : Inv (h ++ suffix) ledger debts locals w :=
  before.views suffix quiet rfl rfl rfl rfl rfl rfl

/-- Exact repayment observer, reusing the existing original-release source
equation. The nested completion observer is a different callback. -/
theorem repayment_run (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event)
    (native : ((releaseCut (some pid)).run w).run a = .ok ((none,v),b)) :
    runWGPrefix (CausalJournal.peerRelease (some pid)) w a h =
      (.ok (((),v),b),h ++ [.stagedDisposal (.release (some pid) ⟨none,w,v,a,b⟩)]) := by
  have source := StagedAdmission.Front.put_run (some pid) w a h
  change runWGPrefix (CausalJournal.peerRelease (some pid)) w a h = _ at source
  rw [native] at source
  exact source

theorem repayment_entry (before : Inv h ledger debts locals w) (pid : PeerId)
    (a b : Ambient) (native : ((releaseCut (some pid)).run w).run a = .ok ((none,v),b)) :
    Inv (h ++ [.stagedDisposal (.release (some pid) ⟨none,w,v,a,b⟩)]) ledger debts locals v := by
  let r : WGRunWitness (Option (PeerId × Peer)) := ⟨none,w,v,a,b⟩
  obtain ⟨epoch,staged⟩ := StagedAdmission.Front.Native.release_none (some pid) r native rfl
  have owned := (ProjectedAction.iff_run_ambient _ _ _).mp
    (StagedAdmission.Front.Ownership.release (some pid)) w a none v b native
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (release_packet_material (some pid)) w a none v b native
  exact before.views [_] (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)
    epoch staged material (congrArg (fun x => x.1.1) owned)
    (congrArg (fun x => x.1.2) owned) (congrArg Prod.snd owned)

/-- The reached source borrow discharges the repayment condition. This
callback returns normally, emits its own nonfinal receipt, and retains every
indexed obligation in the same ledger. -/
theorem repayment_total (before : Inv h ledger debts locals w) (pid : PeerId)
    (funded : Funded pid w) (a : Ambient) :
    ∃ v b, let r : WGRunWitness (Option (PeerId × Peer)) := ⟨none,w,v,a,b⟩
      runWGPrefix (CausalJournal.peerRelease (some pid)) w a h =
        (.ok (((),v),b),h ++ [.stagedDisposal (.release (some pid) r)]) ∧
      r.Valid (releaseCut (some pid)) ∧
      Inv (h ++ [.stagedDisposal (.release (some pid) r)]) ledger debts locals v := by
  obtain ⟨v,b,native⟩ := AllocatedObligation.Publication.release_cut_nonfinal pid funded a
  exact ⟨v,b,repayment_run pid w a h native,native,repayment_entry before pid a b native⟩

def queuedWorld (pid : PeerId) (w : WGWorld) : WGWorld :=
  {w with dev := w.dev.map fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}}

theorem queued_view (pid : PeerId) (w : WGWorld) : StagedEntry.view (queuedWorld pid w) = StagedEntry.view w := by
  unfold StagedEntry.view
  apply Prod.ext
  · cases device : w.dev <;> simp [queuedWorld,Packets.epoch,device]
  apply Prod.ext
  · funext id
    cases device : w.dev <;> simp [queuedWorld,Staged.stagedAt,device]
  apply Prod.ext
  · funext id
    cases device : w.dev <;> simp [queuedWorld,PacketMaterial.view,TxDisposition.txPackets,device]
  apply Prod.ext
  · cases device : w.dev <;> simp [queuedWorld,Packets.snapshot,Packets.deviceStore,device]
  apply Prod.ext
  · funext id
    cases device : w.dev <;> simp [queuedWorld,TxDisposition.txPackets,device]
  · funext id
    cases device : w.dev <;> simp [queuedWorld,txQueueContents,RxCredits.handoffTxView,device]

theorem append_total (before : Inv h ledger debts locals w) (pid : PeerId) (a : Ambient) :
    let r : TimerEffects.Queued (CausalJournal.Context) :=
      ⟨CausalScope.current CausalJournal.scope? h,pid,⟨(),w,queuedWorld pid w,a,a⟩⟩
    runWGPrefix (CausalJournal.effects.append pid) w a h =
      (.ok (((),queuedWorld pid w),a),h ++ [.queued r]) ∧
    r.Valid ∧ Inv (h ++ [.queued r]) ledger debts locals (queuedWorld pid w) := by
  dsimp only
  have native : ((modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}).run w).run a =
      .ok (((),queuedWorld pid w),a) := rfl
  have source := TimerEffects.queue_completed CausalJournal.Event.queued
    (CausalScope.current CausalJournal.scope? h) pid w (queuedWorld pid w) a a h native
  change runWGPrefix (CausalJournal.effects.append pid) w a h = _ at source
  refine ⟨source,native,?_⟩
  exact Inv.history (before.same_view (queued_view pid w)) [_]
    (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queued
