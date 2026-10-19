import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketSource

/-! The actual causal destructor joins packet and reference accounts at one
prepared guard. Native service and positivity remain explicit independent
caller facts; the real guard derives quiescence before reset. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
set_option maxHeartbeats 600000

/-- Native facts at the destructor callback after the real environment guards.
No pending-ticket or staged-empty conclusion is assumed here. -/
structure NativeEntry (w : WGWorld) : Prop where
  clear : Lifecycle.Clear [] [] w
  positive : PeerReference.Inv w
  service : TxWork.Serving [] [] [] w

def Entry (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  CompleteCarrier.Carrier [] [] h w a ∧ NativeEntry w

/-- Both accounts refer to the same observed history and the same native
state immediately before the destructor guards. -/
def Prepared (h : List Event) (w : WGWorld) (_ : Ambient) : Prop :=
  ∃ ledger holders, CompleteRetired.GuardEntry h ledger holders w

theorem prepare_ready : StatePrefixEnsures Entry CompleteProduct.Safe prepareObserved
    (fun _=>Prepared) := by
  intro w a h before
  obtain ⟨suffix,extended,safe,kept⟩ := prepare_checked w a h before.1
  refine ⟨suffix,extended,safe,?_⟩
  cases performed : (runPrefix (prepareObserved.run w) a h).1 with
  | error reason => trivial
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    cases value
    rw [performed] at kept
    have native := (prepare_erases w a h).symm.trans performed
    obtain ⟨ledger,accounted⟩ := kept
    obtain ⟨holders,reference,base,c7,c8⟩ := (hoare_iff_run_ambient _ _ _).mp
      Lifecycle.prepare w a () v b before.2.clear native
    have positive := (hoare_iff_run_ambient _ _ _).mp
      Lifecycle.positive_prepare w a () v b before.2.positive native
    refine ⟨ledger,holders,accounted,
      (hoare_iff_run_ambient _ _ _).mp TxWork.Destruct.prepare_service
        w a () v b before.2.service native,
      reference.funded,reference.upper,?_,c7,c8,?_⟩
    · simpa [base] using reference.funded.aligned.base.symm
    · intro d pid p device found
      exact PeerReference.resident positive device found

/-- The checked native suffix retains its exact guard ledger on return and
its actual accounted journal at Stop. Guard success, rather than a premise,
discharges outstanding packet and staged locations before reset. -/
theorem tail_checked : StatePrefixEnsures Prepared CompleteProduct.Safe
    (liftWGPrefix CompleteRetired.tail) (fun _=>CompleteCarrier.Carrier [] []) := by
  intro w a h before
  obtain ⟨ledger,holders,atGuard⟩ := before
  obtain ⟨suffix,extended,safe,kept⟩ := CompleteRetired.tail_accounted_checked w a h atGuard
  obtain ⟨cut,accounted⟩ := safe
  refine ⟨suffix,extended,CompleteProduct.account_safe ledger _ cut accounted,?_⟩
  cases performed : (runPrefix ((liftWGPrefix CompleteRetired.tail).run w) a h).1 with
  | error reason => trivial
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    rw [performed] at kept
    exact ⟨ledger,kept.1⟩

theorem packet_checked : StatePrefixEnsures Entry CompleteProduct.Safe
    (Driver.destructObserved hooks) (fun _=>CompleteCarrier.Carrier [] []) := by
  rw [source_factor]
  exact StatePrefixEnsures.bind prepare_ready (fun _=>tail_checked)

/-- Actual causal destruction preserves complete packet accounting and the
native allocation companion. Its stopped journal exposes an actual accounted
cut. The reset creates no artificial terminal outcome. -/
theorem checked : StatePrefixEnsures
    (fun h w a=>CompleteAllocated.Carrier [] [] h w a ∧ NativeEntry w)
    CompleteProduct.Safe (Driver.destructObserved hooks)
    (fun _=>CompleteAllocated.Carrier [] []) := by
  intro w a h before
  obtain ⟨suffix,extended,safe,kept⟩ := packet_checked w a h ⟨before.1.1,before.2⟩
  refine ⟨suffix,extended,safe,?_⟩
  cases performed : (runPrefix ((Driver.destructObserved hooks).run w) a h).1 with
  | error reason => trivial
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    rw [performed] at kept
    exact ⟨kept,(hoare_iff_run_ambient _ _ _).mp allocated w a value v b before.1.2
      ((erases w a h).symm.trans performed)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet
