import Leanux.Proofs.WG.TimerDiscipline.HookJournalBridge
import Leanux.Proofs.WG.Noise.PendingTicketHandshakeFrames
import Leanux.Proofs.WG.Noise.PendingTicketStagingFrames
import Leanux.Proofs.WG.Keypairs.Frames.WGMore

/-! Counter projections from existing full snapshot and pending-slot frames, plus immediate state-access frames. No socket, timer or cryptographic traversal is reproduced. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

abbrev CounterSame {α : Type} (action : WG.M α) : Prop :=
  ∀g a value final after,((action.run g).run a)=.ok ((value,final),after)→
    final.keypairCounter=g.keypairCounter

theorem counter_snapshot {α : Type} {action : WG.M α} (same : Keypairs.SameSnapshot action) :
    CounterSame action := by
  intro g a value final after run
  exact congrArg Keypairs.Snapshot.frontier
    ((ProjectedAction.iff_run_ambient _ _ _).mp same g a value final after run)

theorem counter_pending {α : Type} {action : WG.M α}
    (same : SameView Noise.PendingTickets.view action) : CounterSame action := by
  intro g a value final after run
  exact congrArg Lifetimes.Store.frontier
    ((ProjectedAction.iff_run_ambient _ _ _).mp same g a value final after run)

theorem counter_retained {α : Type} {action : WG.M α}
    (same : Noise.PendingTickets.RetainsCall action) : CounterSame action := by
  intro g a value final after run
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp same g a value final after run).1

theorem counter_hook (kind : HookJournal.Hook) (pid : PeerId) :
    CounterSame (HookJournal.action kind pid) := by
  cases kind with
  | handshakeInitiated => exact counter_snapshot (Keypairs.WGTransitions.timersHandshakeInitiated_sameSnapshot pid)
  | dataSent => exact counter_snapshot (Keypairs.WGTransitions.timersDataSent_sameSnapshot pid)
  | dataReceived => exact counter_snapshot (Keypairs.WGTransitions.timersDataReceived_sameSnapshot pid)
  | authenticatedSent => exact counter_snapshot (Keypairs.WGTransitions.timersAnyAuthenticatedPacketSent_sameSnapshot pid)
  | authenticatedReceived => exact counter_snapshot (Keypairs.WGTransitions.timersAnyAuthenticatedPacketReceived_sameSnapshot pid)
  | handshakeComplete site => exact counter_snapshot (Keypairs.WGTransitions.timersHandshakeComplete_sameSnapshot pid site)
  | sessionDerived => exact counter_snapshot (Keypairs.WGTransitions.timersSessionDerived_sameSnapshot pid)
  | traversal => exact counter_snapshot (Keypairs.WGTransitions.timersTraversal_sameSnapshot pid)

theorem counter_ambient {α : Type} (action : AmbientM α) :
    CounterSame (monadLift action : WG.M α) := by
  intro g a value final after run
  cases actual : action.run a with
  | error stop => simp [actual] at run
  | ok result =>
    obtain ⟨x,next⟩:=result
    simp [actual] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩:=run
    rfl
theorem counter_modifyDev (f : Device→Device) : CounterSame (modifyDev f) := by
  intro g a value final after run
  cases value
  have eq : {g with dev:=g.dev.map f}=final := congrArg (fun pair=>pair.1.2) (Except.ok.inj run)
  exact (congrArg WGWorld.keypairCounter eq).symm
theorem counter_modifyPeer (pid : PeerId) (f : Peer→Peer) :
    CounterSame (do setPeer pid (f (←getPeer pid))) := by
  apply counter_snapshot
  exact SameView.bind (Keypairs.WGFrames.getPeer_sameSnapshot pid)
    (fun p=>Keypairs.WGFrames.setPeer_sameSnapshot pid (f p))

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
