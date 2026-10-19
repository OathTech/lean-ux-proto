import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAuxiliaryEntry
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNonDelete

/-! Native reference accounting and TX service accompany the one packet
ledger. Idle operation entries and possibly suspended syscall returns are
distinct predicates; stopped executions require only the reached journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity

def Companions (w : World) : Prop := RetiredPeer.Outer.Boundary w ∧ PeerReference.Inv w.wg

def Ready (h : List Event) (w : World) : Prop :=
  CompleteProduct.Carrier h w ∧ Companions w ∧ TxWork.Serving [] [] [] w.wg ∧ w.ambient.suspended=[]

def Returned (h : List Event) (w : World) : Prop :=
  CompleteProduct.Carrier h w ∧ Companions w ∧ TxWork.At (TxWork.Covered [] []) [] [] w

theorem ready_safe (h : List Event) (w : World) (before : Ready h w) : CompleteProduct.Safe h :=
  CompleteProduct.carrier_safe h w before.1

/-- One actual syscall's native endpoint supplies the auxiliary conjuncts;
its causal observer alone supplies packet accounting and failed-prefix safety. -/
theorem syscall_join (call : Syscall)
    (account : PrefixEnsures Ready CompleteProduct.Safe
      (Driver.syscallObserved hooks call) (fun _ => CompleteProduct.Carrier))
    (native : Framing.Preserves RetiredPeer.Outer.Boundary (Leanux.syscall call)) :
    PrefixEnsures Ready CompleteProduct.Safe (Driver.syscallObserved hooks call) (fun _ => Returned) := by
  intro w h before
  obtain ⟨suffix,history,safe,post⟩ := account w h before
  refine ⟨suffix,history,safe,?_⟩
  cases result : (runPrefix (Driver.syscallObserved hooks call) w h).1 with
  | error reason => trivial
  | ok out =>
    have run := (Native.causal call w h).symm.trans result
    exact ⟨by simpa only [result] using post,
      ⟨(Framing.hoare_iff_run _ _ _).mp native w out.1 out.2 before.2.1.1 run,
      (Framing.hoare_iff_run _ _ _).mp (Native.positive call) w out.1 out.2 before.2.1.2 run⟩,
      TxWork.syscall_boundary_actor call (TxWork.serving_add_suspended before.2.2.1) before.2.2.2 run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
