import Leanux.Proofs.WG.Queues.TxProducerCuts

/-! Exact native cuts of the existing dispatch prefix and activation loop body.
No callbacks, observers, domains, record reads or error arms are changed. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.DispatchCuts
open Leanux Leanux.WG Leanux.Env

def begin (worker : Worker) : Leanux.M (Option Activation) := do
  let d ← getDev
  let mut pid : Option Nat := none
  match worker with
  | .encryptWorker => if d.encryptQueue.empty then return none
  | .decryptWorker => if d.decryptQueue.empty then return none
  | .receiveWorker => if d.handshakeQueue.empty then return none
  | .txWorker =>
    let some headPid := d.txWorkQueue.head? | return none
    let p ← match ← peekUnit .txWorker with
      | some u => resolveUnit .txWorker u d.txWorkQueue
      | none => pure headPid
    modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase p}
    pid:=some p
  | _=>return none
  _ ← hidden (.sectionStart worker)
  return some {worker,pid}

theorem dispatch_factor (worker : Worker) : Env.dispatch worker=(do
    match ← begin worker with
    | none=>return false
    | some a=>Env.Activation.run a;return true) := by
  cases worker <;> unfold Env.dispatch begin
  all_goals simp only [bind_assoc]
  all_goals repeat' first
    | rfl
    | apply RxCredits.bind_congr_source (m:=Leanux.M)
    | (intro x)
    | (split)
    | simp only [bind_assoc,pure_bind]
  all_goals simp_all only [Option.some.injEq,reduceCtorEq]
  all_goals subst_vars
  all_goals simp_all

def body (state : Option Unit × Activation) : Leanux.M (ForInStep (Option Unit × Activation)) := do
  let act := state.2
  match ← Env.Activation.iter act with
  | .ended =>
    _ ← hidden (.sectionStop act.worker)
    return .done (some (),act)
  | .continued => return .yield (none,{act with iterations:=act.iterations+1})
  | .yielded =>
    modifyAmbient fun s=>{s with suspended:=s.suspended++[{act with iterations:=act.iterations+1}]}
    return .done (some (),act)

def run (a : Activation) : Leanux.M Unit := do
  let occupancy ← Env.Activation.occupancy a
  let result ← forIn [0:occupancy+1] (none,a) (fun _ state=>body state)
  match result.1 with
  | some value=>return value
  | none=>invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) in one run"

theorem run_factor (a : Activation) : Env.Activation.run a=run a := by
  unfold Env.Activation.run run body
  dsimp only
  apply RxCredits.bind_congr_source (m:=Leanux.M)
  intro occupancy
  congr 1
  funext i state
  rcases i with ⟨option,act⟩
  cases option with
  | none=>rfl
  | some value=>cases value; rfl

theorem tx_iteration (pid iterations : Nat) :
    Env.Activation.iter {worker:=.txWorker,pid:=some pid,iterations} = (do
      Env.cryptAhead pid
      WG.txIter pid (Env.condResched .txWorker)) := rfl

end Leanux.Proofs.WG.Queues.TxDisposition.DispatchCuts
