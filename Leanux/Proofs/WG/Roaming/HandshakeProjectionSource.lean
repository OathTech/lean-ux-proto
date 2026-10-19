import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.Logged.PrefixState
import Lean

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeProjection
open Leanux Leanux.WG Leanux.Proofs.Logged Origins
variable {E F State : Type}
structure OpsProjects (decode : E → Option F)
    (o : HandshakeSources.Ops (PrefixT E State))
    (p : HandshakeSources.Ops (PrefixT F State)) : Prop where
  step : ∀ {α} (action : WG.M α), ProjectsPrefix decode id (o.step action) (p.step action)
  session : ∀ pid, ProjectsPrefix decode id (o.session pid) (p.session pid)
  modifyPeer : ∀ pid f, ProjectsPrefix decode id (o.modifyPeer pid f) (p.modifyPeer pid f)
  create : ∀ pid, ProjectsPrefix decode id (o.create pid) (p.create pid)
  mac : ∀ pid msg, ProjectsPrefix decode id (o.mac pid msg) (p.mac pid msg)
  send : ∀ pid msg, ProjectsPrefix decode id (o.send pid msg) (p.send pid msg)
  derived : ∀ pid, ProjectsPrefix decode id (o.derived pid) (p.derived pid)
  traversal : ∀ pid, ProjectsPrefix decode id (o.traversal pid) (p.traversal pid)
  sent : ∀ pid, ProjectsPrefix decode id (o.sent pid) (p.sent pid)
  cookie : ∀ msg src, ProjectsPrefix decode id (o.cookie msg src) (p.cookie msg src)
  initiation : ∀ msg, ProjectsPrefix decode id (o.initiation msg) (p.initiation msg)
  response : ∀ msg, ProjectsPrefix decode id (o.response msg) (p.response msg)
  endpoint : ∀ pid src, ProjectsPrefix decode id (o.endpoint pid src) (p.endpoint pid src)
  complete : ∀ pid, ProjectsPrefix decode id (o.complete pid) (p.complete pid)
  keepalive : ∀ pid, ProjectsPrefix decode id (o.keepalive pid) (p.keepalive pid)
  received : ∀ pid, ProjectsPrefix decode id (o.received pid) (p.received pid)
  put : ∀ pid, ProjectsPrefix decode id (o.put pid) (p.put pid)
  cookieConsume : ∀ msg, ProjectsPrefix decode id (o.cookieConsume msg) (p.cookieConsume msg)

elab "handshake_project_intro" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless target.consumeMData.isForall do
    throwError "not an explicit binder"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro x))
elab "handshake_project_leaf" h:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless target.isAppOf ``ProjectsPrefix do throwError "not a projection goal"
  let args := target.getAppArgs
  let action := args[args.size - 2]!
  if action.isAppOf ``HandshakeSources.Ops.step then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).step _))
  else if action.isAppOf ``HandshakeSources.Ops.session then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).session _))
  else if action.isAppOf ``HandshakeSources.Ops.modifyPeer then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).modifyPeer _ _))
  else if action.isAppOf ``HandshakeSources.Ops.create then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).create _))
  else if action.isAppOf ``HandshakeSources.Ops.mac then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).mac _ _))
  else if action.isAppOf ``HandshakeSources.Ops.send then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).send _ _))
  else if action.isAppOf ``HandshakeSources.Ops.derived then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).derived _))
  else if action.isAppOf ``HandshakeSources.Ops.traversal then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).traversal _))
  else if action.isAppOf ``HandshakeSources.Ops.sent then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).sent _))
  else if action.isAppOf ``HandshakeSources.Ops.cookie then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).cookie _ _))
  else if action.isAppOf ``HandshakeSources.Ops.initiation then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).initiation _))
  else if action.isAppOf ``HandshakeSources.Ops.response then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).response _))
  else if action.isAppOf ``HandshakeSources.Ops.endpoint then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).endpoint _ _))
  else if action.isAppOf ``HandshakeSources.Ops.complete then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).complete _))
  else if action.isAppOf ``HandshakeSources.Ops.keepalive then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).keepalive _))
  else if action.isAppOf ``HandshakeSources.Ops.received then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).received _))
  else if action.isAppOf ``HandshakeSources.Ops.put then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).put _))
  else if action.isAppOf ``HandshakeSources.Ops.cookieConsume then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($h).cookieConsume _))
  else throwError "not a callback leaf"
macro "project_handshake_atom" h:ident decode:ident : tactic => `(tactic|
  first
    | handshake_project_leaf $h
    | exact projectsPrefix_pure $decode id _
    | apply projectsPrefix_bind $decode id id
    | (handshake_project_intro; try dsimp only [id])
    | apply projectsPrefix_ite $decode _ id
    | split)

theorem response_projects (decode : E → Option F)
    (o : HandshakeSources.Ops (PrefixT E State))
    (p : HandshakeSources.Ops (PrefixT F State))
    (h : OpsProjects decode o p) (pid : PeerId) :
    ProjectsPrefix decode id (HandshakeSources.responseWith o pid)
      (HandshakeSources.responseWith p pid) := by
  unfold HandshakeSources.responseWith
  repeat' project_handshake_atom h decode

theorem afterMac_projects (decode : E → Option F)
    (o : HandshakeSources.Ops (PrefixT E State))
    (p : HandshakeSources.Ops (PrefixT F State))
    (h : OpsProjects decode o p) (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (mac : MacState) :
    ProjectsPrefix decode id (HandshakeSources.afterMacWith o msg src loaded mac)
      (HandshakeSources.afterMacWith p msg src loaded mac) := by
  unfold HandshakeSources.afterMacWith
  simp only [pure_bind]
  repeat' first
    | exact response_projects decode o p h _
    | project_handshake_atom h decode

theorem reception_projects (decode : E → Option F)
    (o : HandshakeSources.Ops (PrefixT E State))
    (p : HandshakeSources.Ops (PrefixT F State))
    (h : OpsProjects decode o p) (msg : List UInt8) (src : SkbSource) :
    ProjectsPrefix decode id (HandshakeSources.receptionWith o msg src)
      (HandshakeSources.receptionWith p msg src) := by
  unfold HandshakeSources.receptionWith
  repeat' first
    | exact afterMac_projects decode o p h _ _ _ _
    | project_handshake_atom h decode

theorem step_projects (decode : E → Option F)
    (o : HandshakeSources.Ops (PrefixT E State))
    (p : HandshakeSources.Ops (PrefixT F State))
    (h : OpsProjects decode o p) :
    ProjectsPrefix decode id (HandshakeSources.stepWith o)
      (HandshakeSources.stepWith p) := by
  unfold HandshakeSources.stepWith
  apply projectsPrefix_bind decode id id (h.step getDev)
  intro d
  dsimp only [id]
  cases hc : d.handshakeQueue.consume with
  | mk packet ring =>
    cases packet with
    | none =>
      apply projectsPrefix_bind decode id id (h.step (branch .workerConsumed false))
      intro ignored
      exact projectsPrefix_pure decode id false
    | some packet =>
      rcases packet with ⟨msg,src⟩
      apply projectsPrefix_bind decode id id (h.step (branch .workerConsumed true))
      intro ignored
      apply projectsPrefix_bind decode id id (h.step _)
      intro ignored
      apply projectsPrefix_bind decode id id (reception_projects decode o p h msg src)
      intro ignored
      apply projectsPrefix_bind decode id id (h.step _)
      intro ignored
      exact projectsPrefix_pure decode id true
end Leanux.Proofs.WG.Roaming.HandshakeProjection
