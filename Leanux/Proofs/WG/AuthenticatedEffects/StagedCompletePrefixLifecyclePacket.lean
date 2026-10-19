import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixConfigurationDevice
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixTransmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixSendDrain
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketChecked

/-! Prefix safety reaches the real destructor guards through actual removal.
Independent native reference, positivity and service facts remain explicit.
Only the literal journal-silent checked tail reuses an endpoint quiet adapter. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.LifecyclePacket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal
variable (drained : ∀ upTo, Passive.Checked [] [] CompleteProduct.Safe (Driver.sendDrainObserved hooks upTo))
include drained

theorem prepare : Passive.Checked [] [] CompleteProduct.Safe RetiredPeer.Lifecycle.Packet.prepareObserved := by
  unfold RetiredPeer.Lifecycle.Packet.prepareObserved
  exact StateEnsures.bind (Passive.native CompleteProduct.Safe Transmit.account _
    (ReceiveFrames.device _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)))
    (fun _=>StateEnsures.bind (Passive.native CompleteProduct.Safe Transmit.account _
      (ControlFrames.socket (socketReinit_sameSocket none none)))
      (fun _=>Lifecycle.remove_all CompleteProduct.Safe Transmit.account drained))

/-- The same observed preparation also transports the native guard facts;
its actual prefix certificate is supplied separately by `prepare`. -/
theorem prepare_ready : StateEnsures RetiredPeer.Lifecycle.Packet.Entry CompleteProduct.Safe RetiredPeer.Lifecycle.Packet.prepareObserved
    (fun _=>RetiredPeer.Lifecycle.Packet.Prepared) :=
  StateEnsures.join (prepare drained) RetiredPeer.Lifecycle.Packet.prepare_ready (fun _ _ _ before=>before.1)

omit drained in
theorem tail : StateEnsures RetiredPeer.Lifecycle.Packet.Prepared CompleteProduct.Safe
    (liftWGPrefix CompleteRetired.tail) (fun _=>CompleteCarrier.Carrier [] []) :=
  StateEnsures.quiet RetiredPeer.Lifecycle.Packet.tail_checked (fun _ _ _=>rfl)

theorem packet : StateEnsures RetiredPeer.Lifecycle.Packet.Entry CompleteProduct.Safe (Driver.destructObserved hooks)
    (fun _=>CompleteCarrier.Carrier [] []) := by
  rw [RetiredPeer.Lifecycle.Packet.source_factor]
  exact StateEnsures.bind (prepare_ready drained) (fun _=>tail)

/-- Real guard success supplies quiescence; neither staged emptiness nor
absence of pending tickets is an incoming assumption. -/
theorem checked : StateEnsures
    (fun h w a=>CompleteAllocated.Carrier [] [] h w a ∧ RetiredPeer.Lifecycle.Packet.NativeEntry w)
    CompleteProduct.Safe (Driver.destructObserved hooks) (fun _=>CompleteAllocated.Carrier [] []) :=
  StateEnsures.join (packet drained) RetiredPeer.Lifecycle.Packet.checked (fun _ _ _ before=>⟨before.1.1,before.2⟩)

omit drained in
/-- Concrete destruction has no remaining source callback premise. The
independent native guard companions are exactly those of the actual caller. -/
theorem concrete : StateEnsures
    (fun h w a=>CompleteAllocated.Carrier [] [] h w a ∧ RetiredPeer.Lifecycle.Packet.NativeEntry w)
    CompleteProduct.Safe (Driver.destructObserved hooks) (fun _=>CompleteAllocated.Carrier [] []) :=
  checked (SendDrain.checked CompleteProduct.Safe Transmit.account)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.LifecyclePacket
