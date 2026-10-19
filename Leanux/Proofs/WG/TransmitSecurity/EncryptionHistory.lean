import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastDeviceConfiguration
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastTx
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceJournalOuter

/-! A shared-journal carrier joins historical encryption exclusion with actual
physical ownership. Only actual encryption receipts extend its used identities;
quiet native actions retain the same journal projection. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

def used (history : List Journal.Event) : List (Option Nat × SkbId) :=
  (history.filterMap Journal.encryption?).map WorkerEpochs.identity

def Native (past : List (Option Nat × SkbId)) (active : List (List SkbId)) (w : WGWorld) : Prop :=
  EncryptionPast.Ready past active w ∧ OccurrenceStack.Ready [] active w

def StateInv (active : List (List SkbId)) (history : List Journal.Event) (w : WGWorld) : Prop :=
  Native (used history) active w

def Inv (active : List (List SkbId)) (history : List Journal.Event) (w : World) : Prop :=
  StateInv active history w.wg

def Safe (history : List Journal.Event) : Prop := (used history).Nodup

theorem state_safe (before : StateInv active h w) : Safe h := before.1.2.1

theorem safe (before : Inv active h w) : Safe h := state_safe before

theorem initial (net bare : Bool) : StateInv [] [] (Runner.initialWG net bare) :=
  ⟨⟨TxDisposition.LiveFrontier.initial_ready net bare,EncryptionPast.initial _ _⟩,
    OccurrenceLifecycle.initial net bare⟩

theorem product_quiet {g : PrefixM Journal.Event α} {action : Leanux.M α}
    (history : ∀ past, Driver.ProductHistorySafe (fun h => used h = past) g)
    (erases : ErasesPrefix g action)
    (keeps : ∀ past, Preserves (fun w : World => Native past active w.wg) action) :
    PrefixPreserves (Inv active) Safe g := by
  intro w h before
  obtain ⟨suffix,extension,same,_⟩ := history (used h) w h rfl
  have safeAfter : Safe (runPrefix g w h).2 := by
    unfold Safe
    rw [same]
    exact safe before
  refine ⟨suffix,extension,safeAfter,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok output =>
    have after := (hoare_iff_run _ _ _).mp (keeps (used h)) w output.1 output.2 before
      ((erases w h).symm.trans result)
    simpa only [Inv,StateInv,same] using after

theorem state_quiet {g : WGPrefix Journal.Event α} {action : WG.M α}
    (history : ∀ past, Driver.StateHistorySafe (fun h => used h = past) g)
    (erases : ErasesStatePrefix g action)
    (keeps : ∀ past, Preserves (Native past active) action) :
    StatePrefixPreserves (fun h w _ => StateInv active h w) Safe g := by
  intro w a h before
  obtain ⟨suffix,extension,same,_⟩ := history (used h) w a h rfl
  have safeAfter : Safe (runPrefix (g.run w) a h).2 := by
    unfold Safe
    rw [same]
    exact state_safe before
  refine ⟨suffix,extension,safeAfter,?_⟩
  cases result : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok output =>
    have after := (hoare_iff_run_ambient _ _ _).mp (keeps (used h))
      w a output.1.1 output.1.2 output.2 before ((erases w a h).symm.trans result)
    simpa only [StateInv,same] using after

end Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
