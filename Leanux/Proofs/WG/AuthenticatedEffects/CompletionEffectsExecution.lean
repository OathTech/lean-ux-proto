import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeProduct

/-! A delayed TX cause starts at the actual successful crypted-head guard.
The scope contains the chosen ring item's completion, native timer helpers and
socket calls. Selection alone grants no authority: the initialized carrier must
connect this exact item to its earlier packet allocations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def bodySourceWith (o : Ops E) (complete : PeerId → List SkbId → PrefixM E Unit)
    (pid : PeerId) (first : Option (List SkbId)) : PrefixM E Bool := do
  let go ← TxDisposition.andObs (o.step (branch .txPacket first.isSome)) do
    let some f := first | o.step (invariant "unreachable")
    let some h := f.head? | o.step (invariant "an empty ring item")
    o.step (branch .txNotUncrypted ((← o.packet h).state != .uncrypted))
  if !go then return false
  let some item := first | o.step (invariant "unreachable")
  let some headId := item.head? | o.step (invariant "an empty ring item")
  let head ← o.packet headId
  o.drop pid item
  if ← o.step (branch .txCrypted (head.state == .crypted)) then complete pid item
  o.dispose pid item head.keypair

def stepSourceWith (o : Ops E) (complete : PeerId → List SkbId → PrefixM E Unit)
    (pid : PeerId) : PrefixM E Bool := do
  let (first,q) ← o.step ((← o.peer pid).txQueue.peek)
  o.modifyPeer pid fun p => {p with txQueue := q}
  bodySourceWith o complete pid first

theorem bodySource_factor (o : Ops E) (pid : PeerId) (first : Option (List SkbId)) :
    bodySourceWith o (completeWith o) pid first = bodyWith o pid first := rfl

theorem stepSource_factor (o : Ops E) (pid : PeerId) :
    stepSourceWith o (completeWith o) pid = stepWith o pid := rfl

theorem bodySource_projects (ρ : E → Option F) {g : Ops E} {t : Ops F}
    (h : Ops.Projects ρ g t)
    (cg : PeerId → List SkbId → PrefixM E Unit) (ct : PeerId → List SkbId → PrefixM F Unit)
    (hc : ∀ pid item, ProjectsPrefix ρ id (cg pid item) (ct pid item))
    (pid : PeerId) (first : Option (List SkbId)) :
    ProjectsPrefix ρ id (bodySourceWith g cg pid first) (bodySourceWith t ct pid first) := by
  unfold bodySourceWith TxDisposition.andObs
  repeat' first
    | exact hc _ _
    | completion_effects_project h ρ

theorem stepSource_projects (ρ : E → Option F) {g : Ops E} {t : Ops F}
    (h : Ops.Projects ρ g t)
    (cg : PeerId → List SkbId → PrefixM E Unit) (ct : PeerId → List SkbId → PrefixM F Unit)
    (hc : ∀ pid item, ProjectsPrefix ρ id (cg pid item) (ct pid item)) (pid : PeerId) :
    ProjectsPrefix ρ id (stepSourceWith g cg pid) (stepSourceWith t ct pid) := by
  unfold stepSourceWith
  repeat' first
    | with_reducible exact bodySource_projects ρ h cg ct hc _ _
    | completion_effects_project h ρ

def completeScoped (record : CausalScope.Event Cause → E)
    (cause : PeerId → List SkbId → Cause) (o : Ops E) (pid : PeerId) (item : List SkbId) : PrefixM E Unit :=
  CausalScope.prefixScope record (cause pid item) (fun _ => completeWith o pid item)

def stepScoped (record : CausalScope.Event Cause → E)
    (cause : PeerId → List SkbId → Cause) (o : Ops E) (pid : PeerId) : PrefixM E Bool :=
  stepSourceWith o (completeScoped record cause o) pid

theorem completeScoped_projects (ρ : E → Option F) (record : CausalScope.Event Cause → E)
    (cause : PeerId → List SkbId → Cause) (quiet : ∀ e, ρ (record e) = none)
    {g : Ops E} {t : Ops F} (h : Ops.Projects ρ g t) (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ρ id (completeScoped record cause g pid item) (completeWith t pid item) :=
  CausalScope.prefix_projects record (cause pid item) ρ quiet _ _
    (fun _ => complete_projects ρ h pid item)

theorem stepScoped_projects (ρ : E → Option F) (record : CausalScope.Event Cause → E)
    (cause : PeerId → List SkbId → Cause) (quiet : ∀ e, ρ (record e) = none)
    {g : Ops E} {t : Ops F} (h : Ops.Projects ρ g t) (pid : PeerId) :
    ProjectsPrefix ρ id (stepScoped record cause g pid) (stepWith t pid) :=
  stepSource_projects ρ h _ _ (completeScoped_projects ρ record cause quiet h) pid

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
