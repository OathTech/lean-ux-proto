import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceSource
import Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffectsScope
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeProduct
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeScopePrefix
import Leanux.Proofs.WG.AuthenticatedEffects.TimerDispatchScope
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeProjection

/-! Source metadata shared by lexical scopes. Only the fixture constructor
describes a local root. Handshake and candidate scopes need their actual
authentication receipts; timer, completion and send-work scopes need the
carrier for the exact earlier occurrence. None grants permission by itself. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalSources
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The flushed-send cut needs queue order and the selected peer incarnation
and pending flag, not the rest of WGWorld. Absence stays explicit. -/
structure SendEntry where
  queue : Option (List PeerId)
  selected : Option (Nat × Bool)

def sendEntry (pid : PeerId) (w : WGWorld) : SendEntry where
  queue := w.dev.map (·.sendWorkQueue)
  selected := w.dev.bind fun d => (d.peers[pid]?).map fun p => (p.internalId,p.handshakePending)

inductive Cause where
  | fixture (trigger : FixtureEffects.Trigger)
  | handshake (kind : HandshakeCausal.Kind) (peer : PeerId)
  | candidate (id : SkbId) (packet : RxPacket)
  | stackInput (entry : GroOccurrence.Entry)
  | timer (bound : UInt64) (peer : PeerId) (timer : PeerTimer) (entry : WheelEntry)
  | completion (peer : PeerId) (item : List SkbId)
  | sendWork (peer : PeerId) (entry : SendEntry)

def fixtureHooks (record : CausalScope.Event Cause → E) : FixtureEffects.Hooks E :=
  FixtureEffects.scopeHooks record Cause.fixture

def candidateEnter (record : CausalScope.Event Cause → E) (id : SkbId) (packet : RxPacket) : PrefixM E Nat :=
  CausalScope.enterPrefix record (.candidate id packet)

def timerEnter (record : CausalScope.Event Cause → E) (selected : TimerDispatch.Selection → E)
    (device : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) : PrefixM E Nat :=
  TimerDispatch.scope selected device bound pid timer entry
    (CausalScope.enterPrefix record (.timer bound pid timer entry))

def workScope (record : CausalScope.Event Cause → E) (pid : PeerId) (body : WGPrefix E α) : WGPrefix E α :=
  fun w a => CausalScope.scope record (.sendWork pid (sendEntry pid w)) body w a

def flushedWith (record : CausalScope.Event Cause → E) (worker : PeerId → WGPrefix E Unit)
    (pid : PeerId) : WGPrefix E Unit :=
  workScope record pid (HandshakeSecurity.SendExchange.flushedWith liftWGPrefix worker pid)

theorem workScope_projects (record : CausalScope.Event Cause → E) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none)
    (pid : PeerId) (body : WGPrefix E α) (target : WGPrefix F α)
    (projects : StateProjectsPrefix ρ id body target) :
    StateProjectsPrefix ρ id (workScope record pid body) target := by
  intro w a h
  exact CausalScope.withToken_projects record (.sendWork pid (sendEntry pid w)) ρ quiet
    (fun _ => body) target (fun _ => projects) w a h

theorem workScope_run (record : CausalScope.Event Cause → E) (pid : PeerId)
    (body : WGPrefix E α) (w : WGWorld) (a : Ambient) (h : List E) :
    runWGPrefix (workScope record pid body) w a h =
      match runWGPrefix body w a
          (h ++ [record (.entered ⟨h.length,.sendWork pid (sendEntry pid w)⟩)]) with
      | (.error stop,history) => (.error stop,history)
      | (.ok result,history) => (.ok result,history ++ [record (.exited h.length)]) :=
  CausalScope.withToken_run record (.sendWork pid (sendEntry pid w)) (fun _ => body) w a h

theorem workScope_entry (record : CausalScope.Event Cause → E) (pid : PeerId)
    (body : WGPrefix E α) (appends : StateAppends body)
    (w : WGWorld) (a : Ambient) (h : List E) :
    ∃ suffix, (runWGPrefix (workScope record pid body) w a h).2 =
      h ++ record (.entered ⟨h.length,.sendWork pid (sendEntry pid w)⟩) :: suffix :=
  CausalScope.withToken_entry record (.sendWork pid (sendEntry pid w)) (fun _ => body) (fun _ => appends) w a h

theorem timerEnter_projects (record : CausalScope.Event Cause → E) (selected : TimerDispatch.Selection → E)
    (ρ : E → Option F) (quiet : ∀ event, ρ (record event) = none)
    (oldQuiet : ∀ event, ρ (selected event) = none)
    (device : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    ProjectsPrefix ρ (fun _ => 0) (timerEnter record selected device bound pid timer entry) (pure 0) :=
  TimerDispatch.scope_projects selected device bound pid timer entry ρ oldQuiet _
    (CausalScope.enter_projects record (.timer bound pid timer entry) ρ quiet)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalSources
