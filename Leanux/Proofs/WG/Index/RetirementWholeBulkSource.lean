import Leanux.Proofs.WG.Index.RetirementWholeBulkFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- First-pass structural transport complements its existing funded account
and reservation transfer. No cleanup, payment, or second accounting walk occurs. -/
theorem retirementFirstPass_indexFacts :
    Preserves (fun w : WGWorld =>
      ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧
      ∀ d, w.dev = some d → HashSlotCoverage d ∧ HashedOwnersCoherent d)
      retirementFirstPass := by
  let P := fun w : WGWorld =>
    ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧
    ∀ d, w.dev = some d → HashSlotCoverage d ∧ HashedOwnersCoherent d
  have free : Preserves P WG.free := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    exact ⟨(hoare_iff_run_ambient _ _ _).mp
        (ConfiguredRemoval.frame ConfiguredIdentity.allowedipsFree_view)
        w a result v b pre.1 run,
      BaseCoherence.transport pre.2.1
        ((ProjectedAction.iff_run_ambient _ _ _).mp BaseCoherence.free_view
          w a result v b run),
      (hoare_iff_run_ambient _ _ _).mp free_hashSlots_coherent
        w a result v b pre.2.2 run⟩
  have mark (pid : PeerId) : Preserves P (peerMakeDead pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    cases result
    exact ⟨ConfiguredIdentity.peerMakeDead_preserves pid w v a b pre.1 run,
      BaseCoherence.makeDead_preserves pid pre.2.1 a b run,
      (hoare_iff_run_ambient _ _ _).mp (peerMakeDead_hashSlots_coherent pid)
        w a () v b pre.2.2 run⟩
  have getter : Preserves P getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a d v b pre run
    rw [(DecryptCarrier.getDev_current a b run).1]
    exact pre
  have marks (saved : List PeerId) : Preserves P (retirementMarkPass saved) := by
    unfold retirementMarkPass
    apply preserves_bind
    · apply list_view_spec id P
      intro pid accumulator
      exact preserves_bind (hoare_liftAmbient (AmbientM.branch .peerRemoveAllIter1 true) P)
        (fun _ => preserves_bind (mark pid) (fun _ => preserves_pure _))
    · intro _
      exact preserves_pure ()
  unfold retirementFirstPass BaseRemoval.entry
  apply preserves_bind
  · exact preserves_bind free (fun _ =>
      preserves_bind getter (fun d => preserves_pure d.peerList))
  · intro saved
    exact preserves_bind (marks saved) (fun _ => preserves_pure saved)

/-- The same original first-pass return determines the saved slot list and
the complete package for cleanup. Base occurrences become ordered retirement
loans; the cleanup remainder starts from the actual base-empty holder account. -/
theorem retirementFirstPass_work
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (w v : WGWorld) (a b : Ambient) (saved : List PeerId)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (retired ++ loans) w) (stable : StableRx cs w)
    (covered : ∀ d, w.dev = some d → HashSlotCoverage d)
    (coherent : ∀ d, w.dev = some d → HashedOwnersCoherent d)
    (reserved : ∀ d, w.dev = some d → DeadHashedReserved retired d)
    (run : (retirementFirstPass.run w).run a = .ok ((saved,v),b)) :
    saved = holders.base.map Owner.slot ∧
    RetirementWork (holders.withoutBase []) cs
      ((holders.base ++ retired) ++ loans) (holders.base ++ retired) v := by
  obtain ⟨same,fundedAfter,stableAfter,reservedAfter⟩ :=
    retirementFirstPass_step holders cs retired loans w v a b saved
      configured base funded stable reserved run
  obtain ⟨configuredAfter,baseAfter,indexAfter⟩ := (hoare_iff_run_ambient _ _ _).mp
    retirementFirstPass_indexFacts w a saved v b
      ⟨configured,base,fun d device => ⟨covered d device,coherent d device⟩⟩ run
  exact ⟨same,duringWork_initial fundedAfter stableAfter,configuredAfter,baseAfter,
    fun d device => (indexAfter d device).1,
    fun d device => (indexAfter d device).2,reservedAfter⟩

/-- Complete original bulk removal, including both saved loops and their
terminal branches. Each remaining suffix supplies only its actual selected-send
contract. Normal completion pays the saved base occurrences and retains the
prior retirement obligations and external loans; Stops have no final state. -/
theorem peerRemoveAll_retirement
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (send : ∀ done paid tail, holders.base = done ++ paid :: tail →
      SelectedDrain.SendKeeps
        (RetirementWork (holders.withoutBase []) cs
          (paid :: ((tail ++ retired) ++ loans)) (tail ++ retired))
        runFlushedSendWork) :
    Ensures peerRemoveAll
      (fun w => ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧
        holders.Funded cs (retired ++ loans) w ∧ StableRx cs w ∧
        (∀ d, w.dev = some d → HashSlotCoverage d) ∧
        (∀ d, w.dev = some d → HashedOwnersCoherent d) ∧
        (∀ d, w.dev = some d → DeadHashedReserved retired d))
      (fun _ => RetirementWork (holders.withoutBase []) cs (retired ++ loans) retired) := by
  intro w a result v b pre run
  cases result
  rw [peerRemoveAll_retirement_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨saved,marked,c,first,suffix⟩ := run
  obtain ⟨same,work⟩ := retirementFirstPass_work holders cs retired loans w marked a c saved
    pre.1 pre.2.1 pre.2.2.1 pre.2.2.2.1 pre.2.2.2.2.1
      pre.2.2.2.2.2.1 pre.2.2.2.2.2.2 first
  rw [same] at suffix
  exact retirementAfterFirstPass_retirement (holders.withoutBase []) cs retired loans
    holders.base send marked c () v b work suffix

/-- The selected-send callbacks are discharged by the actual funded-send
adapter. The only remaining parameter is the native initiation-index contract
at each genuine cleanup suffix; no replacement callback is executed. -/
theorem peerRemoveAll_retirement_initiation
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (initiation : ∀ done paid tail, holders.base = done ++ paid :: tail →
      ∀ current selected,
        InitiationIndexContract current cs selected (tail ++ retired) (paid :: loans)) :
    Ensures peerRemoveAll
      (fun w => ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧
        holders.Funded cs (retired ++ loans) w ∧ StableRx cs w ∧
        (∀ d, w.dev = some d → HashSlotCoverage d) ∧
        (∀ d, w.dev = some d → HashedOwnersCoherent d) ∧
        (∀ d, w.dev = some d → DeadHashedReserved retired d))
      (fun _ => RetirementWork (holders.withoutBase []) cs (retired ++ loans) retired) := by
  apply peerRemoveAll_retirement holders cs retired loans
  intro done paid tail same
  exact flushedSend_paidRetirementWork (holders.withoutBase []) cs paid
    (tail ++ retired) loans (initiation done paid tail same)

end Leanux.Proofs.WG.Index
