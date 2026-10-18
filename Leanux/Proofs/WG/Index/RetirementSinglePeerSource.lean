import Leanux.Proofs.WG.Index.RetirementWholeBulkSource
import Leanux.Proofs.WG.Index.InitiationIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- One original non-NULL removal pays the unique actual base occurrence.
Its uniqueness follows from the supplied base/account alignment, and the
same make-dead run transfers its stamp before either real work drain. -/
theorem peerRemove_some_retirement
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (pid : PeerId) (selected : pid ∈ holders.base.map Owner.slot) :
    Ensures (peerRemove (some pid))
      (fun w => ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧
        holders.Funded cs (retired ++ loans) w ∧ StableRx cs w ∧
        (∀ d, w.dev = some d → HashSlotCoverage d) ∧
        (∀ d, w.dev = some d → HashedOwnersCoherent d) ∧
        (∀ d, w.dev = some d → DeadHashedReserved retired d))
      (fun _ => RetirementWork
        (holders.withoutBase (BaseRemoval.live holders.base pid))
        cs (retired ++ loans) retired) := by
  intro w a result v b pre run
  cases result
  obtain ⟨paid,slot,one⟩ := unique_detached holders.base pid
    (BaseCoherence.holder_unique pre.2.1 pre.2.2.1.aligned) selected
  change ((peerMakeDead pid >>= fun _ => peerRemoveAfterDead pid).run w).run
    (CounterWindow.record a .peerRemoveNull false) = .ok (((),v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,marked,c,mark,pay⟩ := run
  cases u
  obtain ⟨funded,stable,configured,base,reserved⟩ := peerMakeDead_retirement_step
    pid holders cs retired loans w marked
      (CounterWindow.record a .peerRemoveNull false) c
      pre.1 pre.2.1 pre.2.2.1 pre.2.2.2.1 pre.2.2.2.2.2.2 mark
  have index := (hoare_iff_run_ambient _ _ _).mp
    (peerMakeDead_hashSlots_coherent pid) w
      (CounterWindow.record a .peerRemoveNull false) () marked c
      (fun d device => ⟨pre.2.2.2.2.1 d device,pre.2.2.2.2.2.1 d device⟩) mark
  have work : RetirementWork
      (holders.withoutBase (BaseRemoval.live holders.base pid))
      cs (paid :: (retired ++ loans)) (paid :: retired) marked := by
    refine ⟨duringWork_initial ?_ stable,configured,base,
      fun d device => (index d device).1,
      fun d device => (index d device).2,?_⟩
    · simpa only [one,List.singleton_append,List.cons_append,List.nil_append] using funded
    · simpa only [one,List.singleton_append] using reserved
  exact peerRemoveAfterDead_retirement_actual
    (holders.withoutBase (BaseRemoval.live holders.base pid))
    cs paid retired loans
    marked c () v b work (by simpa only [slot] using pay)

/-- The original NULL branch still records its decision, returns immediately,
and retains the complete supplied account and index package. -/
theorem peerRemove_none_retirement
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations) :
    Ensures (peerRemove none)
      (fun w => ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧
        holders.Funded cs (retired ++ loans) w ∧ StableRx cs w ∧
        (∀ d, w.dev = some d → HashSlotCoverage d) ∧
        (∀ d, w.dev = some d → HashedOwnersCoherent d) ∧
        (∀ d, w.dev = some d → DeadHashedReserved retired d))
      (fun _ => RetirementWork holders cs (retired ++ loans) retired) := by
  intro w a result v b pre run
  cases result
  change Except.ok (((),w),CounterWindow.record a .peerRemoveNull true) =
    .ok (((),v),b) at run
  cases run
  exact ⟨duringWork_initial pre.2.2.1 pre.2.2.2.1,pre.1,pre.2.1,
    pre.2.2.2.2.1,pre.2.2.2.2.2.1,pre.2.2.2.2.2.2⟩

/-- A live resident supplies its own stamped base occurrence from configured
identity and funded base coherence. It need not be supplied as a separate
selection assumption. The original removal may still refuse or stop. -/
theorem peerRemove_live_retirement
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (pid : PeerId) :
    Ensures (peerRemove (some pid))
      (fun w => ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧
        holders.Funded cs (retired ++ loans) w ∧ StableRx cs w ∧
        (∀ d, w.dev = some d → HashSlotCoverage d) ∧
        (∀ d, w.dev = some d → HashedOwnersCoherent d) ∧
        (∀ d, w.dev = some d → DeadHashedReserved retired d) ∧
        ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ p.isDead = false)
      (fun _ => RetirementWork
        (holders.withoutBase (BaseRemoval.live holders.base pid))
        cs (retired ++ loans) retired) := by
  intro w a result v b pre run
  obtain ⟨d,p,device,resident,live⟩ := pre.2.2.2.2.2.2.2
  have selected : pid ∈ holders.base.map Owner.slot :=
    List.mem_map.mpr ⟨⟨d.ifindex,pid,p.internalId⟩,
      FundedBase.live_base_reservation pre.1 pre.2.1 pre.2.2.1 device resident live,rfl⟩
  exact peerRemove_some_retirement holders cs retired loans pid selected w a result v b
    ⟨pre.1,pre.2.1,pre.2.2.1,pre.2.2.2.1,pre.2.2.2.2.1,
      pre.2.2.2.2.2.1,pre.2.2.2.2.2.2.1⟩ run

end Leanux.Proofs.WG.Index
