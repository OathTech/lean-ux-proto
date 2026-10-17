import Leanux.Proofs.WG.Packets.PublicationIngressNative
import Leanux.Proofs.WG.Origins.ConfiguredMaintenance

/-! Session establishment retains existing encrypted packet publications. The
actual allocating front changes the key frontier, so only its RX and configured
fields are projected; no key-allocation frame is assumed for that front. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

theorem sessionFront_rx (pid : PeerId) :
    SameView RxDisposition.nativeRxStore (SessionOrigin.front pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hr
  cases result with
  | none =>
    exact congrArg RxDisposition.nativeRxStore
      (Origins.front_none pid w v ambient finalAmbient hr)
  | some ctx =>
    obtain ⟨before,after,hb,ha,_,_,rx⟩ :=
      (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.front_device)
        pid ctx w v ambient finalAmbient hr
    have configured := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ConfiguredSession.front_view pid) w ambient (some ctx) v finalAmbient hr
    have epoch := congrArg (fun s : Option ConfiguredIdentity.State => s.map (·.epoch)) configured
    simpa only [RxDisposition.nativeRxStore,hb,ha,Option.map_some,Option.bind_some,rx] using
      congrArg (fun e : Option Nat => (e,fun id => before.rxSkbs[id]?))
        (show some after.ifindex = some before.ifindex from by
          simpa only [ConfiguredIdentity.view,ConfiguredIdentity.state,hb,ha,
            Option.map_some] using epoch)

private theorem addNewKeypair_geometry (pid kp : Nat) :
    SameView OwnerCompletion.geometry (addNewKeypair pid kp) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' completion_step initial

theorem sessionTail_geometry (pid kp : Nat) :
    SameView OwnerCompletion.geometry (SessionOrigin.tail pid kp) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold SessionOrigin.tail SessionOrigin.tailWith handshakeZero
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (allocation_release_head addNewKeypair
       exact (addNewKeypair_geometry _ _).wp (fun s => s = initial))
    | (allocation_release_head liftIndex
       apply hoare_liftIndex
       intro w d table hi hd
       simpa only [OwnerCompletion.geometry,RxCredits.rxView,hd,Option.map_some,
         Option.bind_some] using hi)
    | completion_step initial

theorem beginSession_rx (pid : PeerId) :
    SameView RxDisposition.nativeRxStore (beginSession pid) := by
  rw [SessionOrigin.factor]
  apply SameView.bind (sessionFront_rx pid)
  intro ctx
  cases ctx with
  | none => exact SameView.pure _ _
  | some ctx => exact (sessionTail_geometry pid ctx.slot).factor Prod.snd

theorem beginSession_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (beginSession pid) :=
  preserves_of_configured _ (beginSession_rx pid) (ConfiguredMaintenance.beginSession_view pid) history

end Leanux.Proofs.WG.PublicationFrontier
