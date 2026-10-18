import Leanux.Proofs.WG.AuthenticatedEffects.Socket4Source
import Leanux.Proofs.WG.AuthenticatedEffects.Socket6CachedSource

/-! The actual transport tunnel prefix, with both loopback modes, ends before
the sole datagram append. Routing/cache stages reuse the native source factors. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Completion
open Leanux Leanux.WG Lifetimes AuthenticatedEffects

def tunnelFront (e : Endpoint) (bytes : List UInt8) (r : Route) (exactRx : Bool) : WG.M Nat := do
  if r.dev == WG0_IFINDEX then unsupported "a datagram routed back into wg0"
  if exactRx then loopbackSend ([.ipIdentKey,.ipIdentReserve,.flowHashSecret] ++ allocCuts) true
  else skipCut [.ipIdentKey,.ipIdentReserve,.flowHashSecret,.sectionStart .netRx,.sectionStop .netRx]
  modifyDev fun d => {d with txPackets := d.txPackets + 1,txBytes := d.txBytes + bytes.length}
  socketPort e.family

theorem tunnel_factor (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    tunnelXmitSource e bytes ds r exactRx = (do
      let sport ← tunnelFront e bytes r exactRx
      modify fun w => {w with sent := w.sent ++ [tunnelDatagram e bytes ds r sport]}) := by
  unfold tunnelXmitSource tunnelFront tunnelDatagram
  by_cases route : r.dev == WG0_IFINDEX
  all_goals cases exactRx <;> simp only [route,Bool.false_eq_true,↓reduceIte,bind_assoc]

set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem invariant_bind (s : String) (f : α → WG.M β) :
    ((invariant s : WG.M α) >>= f) = invariant s := rfl

open Lean Meta Elab Tactic in
elab "socket_factor_intro" : tactic => do
  let (fid,goal) ← (← getMainGoal).intro1
  replaceMainGoal [goal]
  withMainContext do
    let ty ← whnf (← inferType (.fvar fid))
    if ty.isAppOf ``Bool || ty.isAppOf ``Option || ty.isAppOf ``Except then
      let branches ← goal.cases fid
      replaceMainGoal (branches.toList.map (·.mvarId))

open Lean Meta Elab Tactic in
elab "socket_bind_head" : tactic => withMainContext do
  let ty := (← instantiateMVars (← getMainTarget)).consumeMData
  unless ty.isAppOf ``Eq do throwError "not an equality"
  let args := ty.getAppArgs
  unless args[1]!.isAppOf ``Bind.bind && args[2]!.isAppOf ``Bind.bind do
    throwError "not two binds"

theorem socket4Front_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    send4Source e cache bytes ds exactRx = (socket4Front e cache bytes ds exactRx >>= socketResult e bytes ds exactRx) := by
  cases cache <;> unfold send4Source socket4Front
  all_goals simp only [socket4AfterCacheFront_factor,bind_assoc,if_bind,invariant_bind,pure_bind]
  all_goals repeat' first
    | with_reducible rfl
    | (socket_bind_head; with_reducible apply source_bind)
    | socket_factor_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split
  all_goals rfl

theorem socket6_factor (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    send6 e cache bytes ds exactRx = (do
      match ← socket6Front e cache with
      | .error err => pure err
      | .ok r => tunnelXmitSource e bytes ds r exactRx; pure 0) :=
  Socket6Cached.factor e cache bytes ds exactRx

end Leanux.Proofs.WG.TransmitSecurity.Completion
