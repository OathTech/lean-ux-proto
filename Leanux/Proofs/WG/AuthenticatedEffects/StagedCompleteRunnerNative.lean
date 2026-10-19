import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNativeCallbacks
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverProjection
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceDispatch

/-! Native normal companions are joined only by exact result erasure.
No equality between the independent observer histories is asserted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity HandshakeSecurity

theorem neutral (call : Syscall) :
    ErasesPrefix (Driver.syscallObserved NativeDriver.hooks call) (Leanux.syscall call) := by
  intro w h
  have empty : h=[] := by cases h with | nil => rfl | cons e _ => cases e
  subst h
  have projected := congrArg Prod.fst
    (Driver.syscall_projects NativeDriver.nonce_projection call w ([] : List Nonce.Allocation))
  simp only [List.filterMap_nil] at projected
  rw [Driver.nonce_syscallObserved_eq,Nonce.syscallObserved_erases] at projected
  exact projected.trans (by cases (Leanux.syscall call).run w <;> rfl)

theorem exchange (call : Syscall) :
    ErasesPrefix (Driver.syscallObserved ExchangeDriver.hooks call) (Leanux.syscall call) :=
  CausalJournal.CallbackFrames.product_erases NativeDriver.erase
    (Driver.syscall_projects ExchangeDriver.native_projection call) (neutral call)

theorem causal (call : Syscall) :
    ErasesPrefix (Driver.syscallObserved CausalJournal.hooks call) (Leanux.syscall call) := by
  apply CausalJournal.CallbackFrames.product_erases CausalJournal.old? (CausalJournal.syscall_projects call)
  apply CausalJournal.CallbackFrames.product_erases Journal.nonce?
    (Driver.syscall_projects Journal.hooks_projects call)
  rw [Driver.nonce_syscallObserved_eq]
  exact Nonce.syscallObserved_erases call

theorem positive (call : Syscall) :
    Preserves (fun w : World => PeerReference.Inv w.wg) (Leanux.syscall call) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have post := (PeerReference.syscall (E:=Exchange.Event) call w []
    ⟨PeerReference.safe_nil,before⟩).choose_spec.2.2
  have native : (runPrefix (Driver.syscallObserved (PeerReference.EntrySource.hooks (E:=Exchange.Event)) call) w []).1
      =.ok (result,v) := (exchange call w []).trans run
  rw [native] at post
  exact post.2

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner.Native
