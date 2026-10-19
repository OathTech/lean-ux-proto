import Leanux.Proofs.WG.AuthenticatedEffects.CausalSourceMetadata
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsNeutral
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeErasure

/-! The selected handshake-send worker inherits its actual queue occurrence.
Its timer arms are exposed without replacing exchange creation, MAC or send
callbacks; those may carry additional receipts on this same source spine. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendEffects
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def native : Ops (WGPrefix E) where
  step := liftWGPrefix
  create := fun pid => liftWGPrefix (createInitiation pid)
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  initiated := fun pid => liftWGPrefix (timersHandshakeInitiated pid)
  put := fun peer => liftWGPrefix (peerPut peer)

def withEffects (base : Ops (WGPrefix E)) (effects : TimerEffects.Ops (WGPrefix E)) : Ops (WGPrefix E) :=
  {base with
    traversal := fun pid => TimerEffects.traversalWith effects pid
    initiated := fun pid => TimerEffects.initiatedWith effects pid}

def flushed (record : CausalScope.Event CausalSources.Cause → E)
    (base : Ops (WGPrefix E)) (effects : TimerEffects.Ops (WGPrefix E)) (pid : PeerId) : WGPrefix E Unit :=
  CausalSources.flushedWith record (workerWith (withEffects base effects)) pid

theorem effects_projects (ρ : E → Option F)
    {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)} (h : Ops.Projects ρ g t)
    {eg : TimerEffects.Ops (WGPrefix E)} {et : TimerEffects.Ops (WGPrefix F)}
    (he : TimerEffects.Ops.Projects ρ eg et) :
    Ops.Projects ρ (withEffects g eg) (withEffects t et) :=
  {h with
    traversal := TimerEffects.traversal_projects ρ he
    initiated := TimerEffects.initiated_projects ρ he}

theorem effects_neutral : withEffects (native : Ops (WGPrefix E)) TimerEffects.lifted = native := by
  simp only [withEffects,TimerEffects.traversal_lifted,TimerEffects.initiated_lifted,native]

private theorem lift_projects (ρ : E → Option F) (action : WG.M α) :
    StateProjectsPrefix ρ id (liftWGPrefix action) (liftWGPrefix action) := by
  intro w a h
  change ((action.run w).run a,h.filterMap ρ) =
    (((action.run w).run a).map (fun ((x,v),b) => ((x,v),b)),h.filterMap ρ)
  cases (action.run w).run a <;> rfl

theorem native_projects (ρ : E → Option F) :
    Ops.Projects ρ (native : Ops (WGPrefix E)) (native : Ops (WGPrefix F)) := by
  constructor
  all_goals intros
  all_goals exact lift_projects ρ _

theorem flushed_projects (ρ : E → Option F)
    (record : CausalScope.Event CausalSources.Cause → E) (quiet : ∀ event, ρ (record event) = none)
    {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)} (h : Ops.Projects ρ g t)
    {eg : TimerEffects.Ops (WGPrefix E)} {et : TimerEffects.Ops (WGPrefix F)}
    (he : TimerEffects.Ops.Projects ρ eg et) (pid : PeerId) :
    StateProjectsPrefix ρ id (flushed record g eg pid)
      (HandshakeSecurity.SendExchange.flushedWith liftWGPrefix (workerWith (withEffects t et)) pid) :=
  CausalSources.workScope_projects record ρ quiet pid _ _
    (HandshakeSecurity.SendExchange.flushed_projects ρ liftWGPrefix liftWGPrefix (lift_projects ρ)
      _ _ (worker_projects ρ (effects_projects ρ h he)) pid)

theorem native_erases : Ops.Erases (native : Ops (WGPrefix E)) := by
  constructor
  all_goals intros
  all_goals exact erasesStatePrefix_lift _

private theorem lift_frame (action : WG.M α) :
    StateHistoryFrame some (liftWGPrefix action : WGPrefix E α) := fun _ _ _ => rfl

theorem native_flushed_equal (pid : PeerId) :
    HandshakeSecurity.SendExchange.flushedWith liftWGPrefix
      (workerWith (native : Ops (WGPrefix E))) pid = liftWGPrefix (runFlushedSendWork pid) := by
  apply TimerEffects.eq_native_lift
  · exact HandshakeSecurity.SendExchange.flushed_erases liftWGPrefix erasesStatePrefix_lift _
      (worker_erases native_erases) pid
  · unfold HandshakeSecurity.SendExchange.flushedWith afterTakeWith workerWith sendWith
    simp only [native]
    repeat' first
      | with_reducible exact lift_frame _
      | (change StateHistoryFrame some (pure _); exact fun _ _ _ => rfl)
      | with_reducible apply StateHistoryFrame.bind
      | contradiction
      | split
      | (session_origin_intro_forall; try dsimp only)

theorem flushed_native_projects (ρ : E → Option F)
    (record : CausalScope.Event CausalSources.Cause → E) (quiet : ∀ event, ρ (record event) = none)
    {g : Ops (WGPrefix E)} (h : Ops.Projects ρ g native)
    {effects : TimerEffects.Ops (WGPrefix E)} (he : TimerEffects.Ops.Projects ρ effects TimerEffects.lifted)
    (pid : PeerId) :
    StateProjectsPrefix ρ id (flushed record g effects pid) (liftWGPrefix (runFlushedSendWork pid)) := by
  have projected := flushed_projects ρ record quiet h he pid
  simpa only [effects_neutral,native_flushed_equal] using projected

end Leanux.Proofs.WG.AuthenticatedEffects.SendEffects
