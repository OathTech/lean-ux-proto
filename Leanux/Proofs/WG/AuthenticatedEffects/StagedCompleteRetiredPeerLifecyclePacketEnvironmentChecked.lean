import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketEnvironmentFrames

/-! Actual environment deletion joins the native idle/dump guards, counted
shutdown and the checked destructor. Incoming emptiness is not assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet.Environment
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
open HolderDeviceCreate
set_option maxHeartbeats 600000

/-- The initialized caller supplies independent physical, reference, positive
and service facts. The actual guard must discharge the receive carrier. -/
def Entry (cs : RxCredits.Ledger) (h : List Event) (w : World) : Prop :=
  CompleteProduct.Carrier h w ∧ ExactBoundary cs [] w.wg ∧ OptionalPhysical w.wg ∧
    PeerReference.Inv w.wg ∧ TxWork.Serving [] [] [] w.wg

theorem guards_checked : PrefixEnsures (Entry cs) CompleteProduct.Safe
    (liftPrefix HolderDeviceDelete.guards) (fun _=>Ready) := by
  apply PrefixEnsures.lift _ (fun h w before=>CompleteProduct.carrier_safe h w before.1)
  intro h w value v before run
  cases value
  obtain ⟨same,empty,clear⟩ := Lifecycle.delete_guards before.2.1 before.2.2.1 run
  subst v
  subst cs
  exact ⟨before.1,clear,before.2.2.2.1,before.2.2.2.2⟩

theorem destructor_checked : PrefixEnsures Ready CompleteProduct.Safe
    (liftWGObserver (Driver.destructObserved hooks)) (fun _=>CompleteProduct.Carrier) :=
  Packet.checked.liftWGObserver

/-- Every native branch of actual observed deletion preserves the complete
packet account on normal return, and its actual accounted journal on Stop.
No idle, staged-empty or no-pending premise is supplied. The same guard and
shutdown execution establish the native prerequisites used by destruction. -/
theorem checked : PrefixEnsures (Entry cs) CompleteProduct.Safe
    (Driver.envDeleteObserved hooks) (fun _=>CompleteProduct.Carrier) := by
  rw [source_factor]
  apply PrefixEnsures.bind guards_checked
  intro _
  apply PrefixEnsures.bind (Q:=fun (_ : WGWorld)=>Ready) (quiet getWG (fun initial=>productGetWG_spec (·=initial)))
  intro w
  split
  · exact PrefixEnsures.pure (fun h w before=>CompleteProduct.carrier_safe h w before.1)
      (fun _ _ before=>before.1)
  · apply PrefixEnsures.bind (Q:=fun (_ : Unit)=>Ready) prefix_checked
    intro _
    exact PrefixEnsures.bind destructor_checked (fun _=>CompleteProduct.pure_checked 0)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet.Environment
