import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointCoverage

/-! Explicit option tails avoid dependent tactic-generated matcher transports.
Each equation identifies the original source, with the same guards and order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver
open Points

def upNotifications : Bool → PrefixM Event Unit
  | false => pure ()
  | true => do
      liftPrefix Net.Fib.rtCacheFlush
      liftPrefix (Net.Fib.netdevUp WG0_IFINDEX)
      liftPrefix (modifyEnv fun w=>{w with routesPending:=true})

def upFinish (ret : Int) : PrefixM Event Int := do
  liftPrefix (skipCut allocCuts)
  upNotifications (ret == 0)
  pure ret

def upActive : Bool → PrefixM Event Int
  | true => pure 0
  | false => do
      let ret ← liftWGObserver (upObserved hooks)
      upFinish ret

def upTail : Option Device → PrefixM Event Int
  | none => pure (-ENODEV)
  | some d => upActive d.running

def up : PrefixM Event Int := do
  let saved ← liftPrefix getWG
  upTail saved.dev

def downBody : PrefixM Event Int := do
  liftPrefix Env.requireIdleDevice
  liftWGObserver (downObserved hooks)
  liftPrefix (skipCut allocCuts)
  liftPrefix Net.Fib.rtCacheFlush
  liftPrefix (Net.Fib.netdevDown WG0_IFINDEX)
  liftPrefix (modifyRouting fun w=>{w with defaultRoute6:=false,addrs6:=[],ipv6Gen:=w.ipv6Gen+1})
  pure 0

def downActive : Bool → PrefixM Event Int
  | false => pure 0
  | true => downBody

def downTail : Option Device → PrefixM Event Int
  | none => pure (-ENODEV)
  | some d => downActive d.running

def down : PrefixM Event Int := do
  let saved ← liftPrefix getWG
  downTail saved.dev

def deleteTail (absent : Bool) : PrefixM Event Int :=
  if absent then pure (-ENODEV) else do
    RetiredPeer.Lifecycle.Packet.Environment.prefixObserved
    liftWGObserver (destructObserved hooks)
    pure 0

def delete : PrefixM Event Int := do
  liftPrefix RxCredits.HolderDeviceDelete.guards
  let saved ← liftPrefix getWG
  deleteTail saved.dev.isNone

theorem up_source : envUpObserved hooks=up := by
  unfold envUpObserved up
  congr 1
  funext saved
  cases saved.dev with
  | none => rfl
  | some d =>
    cases running : d.running
    · simp only [upTail,running,Bool.false_eq_true,ite_false,upActive]
      apply congrArg (Bind.bind (liftWGObserver (upObserved hooks)))
      funext ret
      unfold upFinish
      apply congrArg (Bind.bind (liftPrefix (skipCut allocCuts)))
      funext ignored
      cases enabled : ret == 0 <;>
        simp only [Bool.false_eq_true,ite_false,ite_true,upNotifications,pure_bind,bind_assoc]
    · simp only [upTail,running,ite_true,upActive]

theorem down_source : envDownObserved hooks=down := by
  unfold envDownObserved SendExchange.envDownWith down
  congr 1
  funext saved
  cases saved.dev with
  | none => rfl
  | some d => cases running : d.running <;> simp only [downTail,running,downActive,downBody,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]

theorem delete_source : envDeleteObserved hooks=delete :=
  RetiredPeer.Lifecycle.Packet.Environment.source_factor

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
