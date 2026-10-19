import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxAllocationFrames
import Leanux.Proofs.WG.Queues.HolderAdmission

/-! Native RX publication acquires and repays its own transient reference.
The account uses the actual resolved peer, including the EPIPE publication
arm, and does not assume it equals an arbitrary stored owner. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem Phased.publication (account : Phased holders carriers loans w)
    (id : SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerRx (pure () : WG.M Unit) id state).run w).run a = .ok (((),v),b)) :
    Phased holders carriers loans v := by
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderAdmission.publication_frame id state w)
    w a () v b (Frame.refl w) run
  refine ⟨⟨account.funded.aligned.frame frame,publication_state account.funded.carriers a b run⟩,?_⟩
  intro owner
  rw [publication_balances id state w v a b run]
  exact account.upper owner

theorem Phased.publish_dead {c : RxCredits.Carrier}
    (account : Phased holders (c :: carriers) loans w)
    (stable : StableRx carriers w) (phase : c.phase = .queued)
    (a b : Ambient)
    (run : ((enqueuePerPeerRx (pure () : WG.M Unit) c.packet.slot .dead).run w).run a =
      .ok (((),v),b)) :
    Account holders (c :: carriers) loans v :=
  (account.publication c.packet.slot .dead a b run).boundary
    (stable_publication stable account.funded.carriers phase a b run)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
