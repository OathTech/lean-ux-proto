import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTakeFrames

/-! Entry-to-selected source composition. The native packet bounds and owner
census travel with the same fixed ticket ledger from the actual take through
borrowing and the checked nonce loop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance RetirementSecurity
open HandshakeSecurity.StagedConservation

theorem taken (r : Take.Receipt) (native : r.Valid) (chosen : r.run.value = some peer)
    (before : StagedEntry.Inv history ledger debts locals r.run.before) :
    ∃ after generation, Step ledger after ∧ Ready after debts locals generation r.pid peer history.length
      (history ++ [.stagingTaken r]) r.run.after r.run.ambientAfter := by
  obtain ⟨after,generation,step,held⟩ := SoundHeld.taken r native chosen before.core
    before.justified before.allocationLinks before.noSelected
  exact ⟨after,generation,step,held,StagedEntry.TakeFrames.physical before native⟩

theorem borrow (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (Safe : List Event → Prop)
    (frontier : ∀ h, SoundHeld.Active ledger debts generation pid peer position h → Safe h) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (liftWGPrefix (Take.borrow (some peer)))
      (fun selected h w a => ∃ keypair, selected = some (peer,keypair) ∧
        Ready ledger debts locals generation pid peer position h w a) := by
  have physical : Preserves (NativeReady.Inv locals) (Take.borrow (some peer)) := by
    unfold Take.borrow
    exact preserves_bind (NativeReady.get_key peer.keypairCurrent) (fun _ => preserves_pure _)
  intro w a h before
  obtain ⟨suffix,extended,safe,post⟩ :=
    SoundHeld.borrow ledger debts generation pid peer position Safe frontier w a h before.toSound
  refine ⟨suffix,extended,safe,?_⟩
  cases result : (runPrefix ((liftWGPrefix (Take.borrow (some peer))).run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have nativeRun : ((Take.borrow (some peer)).run w).run a = .ok ((value,v),b) := result
    rw [result] at post
    obtain ⟨keypair,chosen,held⟩ := post
    exact ⟨keypair,chosen,held,
      (hoare_iff_run_ambient _ _ _).mp physical w a value v b before.native nativeRun⟩

theorem selected_event (before : Ready ledger debts locals generation pid peer position h w a)
    (run : WGRunWitness (Option (Peer × Option KeypairId))) :
    Ready ledger debts locals generation pid peer position
      (h ++ [Event.old (.responder (.selected pid run))]) w a :=
  ⟨SoundHeld.selected_event before.toSound run,before.native⟩

/-- The allocation preconditions now follow the actual selected source from
one incoming entry bundle. Its consuming no-key and submit callbacks remain
explicit; the theorem does not assume that the containing run succeeds. -/
theorem after_take (r : Take.Receipt) (native : r.Valid) (chosen : r.run.value = some peer)
    (before : StagedEntry.Inv history ledger debts locals r.run.before)
    (Safe : List Event → Prop) (Post : List Event → WGWorld → Ambient → Prop)
    (postSafe : ∀ h w a, Post h w a → Safe h) :
    ∃ after generation, Step ledger after ∧
      ((∀ h, SoundHeld.Active after debts generation r.pid peer history.length h → Safe h) →
      (∀ kp invalid, StatePrefixEnsures
        (Ready after debts locals generation r.pid peer history.length) Safe
        (HeldSource.noKey r.pid peer kp invalid) (fun _ => Post)) →
      (∀ kid packets, StatePrefixEnsures
        (fun h w a => Ready after debts locals generation r.pid peer history.length h w a ∧
          BatchPayload.Shape r.pid kid peer.staged packets) Safe
        (HeldSource.submit r.pid kid packets) (fun _ => Post)) →
      let out := runWGPrefix (Driver.stagingObserved hooks r.pid) r.run.before r.run.ambientBefore history
      ∃ suffix, out.2 = (history ++ [.stagingTaken r]) ++ suffix ∧ Safe out.2 ∧
        match out.1 with
        | .error _ => True
        | .ok ((_,w),a) => Post out.2 w a) := by
  obtain ⟨after,generation,step,held⟩ := taken r native chosen before
  refine ⟨after,generation,step,?_⟩
  intro frontier rejected submitted
  exact SelectionCarrier.after_take r native chosen
    (Ready after debts locals generation r.pid peer history.length) Safe
    (fun _ _ _ before => frontier _ before.toSound.active) held
    (borrow after debts locals generation r.pid peer history.length Safe frontier)
    (fun _ _ _ run before => selected_event before run) Post
    (fun keypair => checked after debts locals generation r.pid peer history.length keypair Safe frontier
      Post postSafe (HeldSource.noKey r.pid peer) (HeldSource.submit r.pid) rejected submitted)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
