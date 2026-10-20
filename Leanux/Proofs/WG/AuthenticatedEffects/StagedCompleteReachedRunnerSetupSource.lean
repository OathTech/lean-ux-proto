import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerStoreCanonical

/-! Setup factors preserve the original component-only prefill and routing
boot, including error index zero and the post-boot observation reset. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PrefixStore
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open Queues.RxCredits

def prefillBodyWith (count : Nat)
    (work : SeccompWorld → TaskWorld → Except String (SeccompWorld × TaskWorld)) : Leanux.M Unit := do
  let w ← (get : Leanux.M World)
  if count > 0 then
    match work w.seccomp w.tasks with
    | .ok (seccomp,tasks) => modify fun v=>{v with seccomp,tasks}
    | .error reason => throw (.invariant reason)

def prefillBody (count : Nat) : Leanux.M Unit :=
  prefillBodyWith count (Env.seccompPrefill count)

def bootBody (net foreign : Bool) : Leanux.M Unit := do
  if net then
    Net.Fib.bootTables
    if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables
    modifyAmbient fun a=>{a with steps:=#[],envCalls:=[]}

noncomputable def prefillNativeShape (count : Nat) : ProductStore.Shape (prefillBody count) := by
  unfold prefillBody prefillBodyWith
  repeat' control_store_step

noncomputable def bootNativeShape (net foreign : Bool) : ProductStore.Shape (bootBody net foreign) := by
  unfold bootBody
  repeat' control_store_step

noncomputable def prefillShape (count : Nat) : Shape (liftPrefix (prefillBody count)) :=
  .native (prefillNativeShape count)

noncomputable def bootShape (net foreign : Bool) : Shape (liftPrefix (bootBody net foreign)) :=
  .native (bootNativeShape net foreign)

theorem setup_run (body : Leanux.M Unit) (w : World) (h : List Event) :
    runPrefixOuter (do let out ← runAtPrefix 0 w (liftPrefix body);pure out.2) h =
      ((body.run w).map Prod.snd |>.mapError (fun e=>(0,e)),h) := by
  rw [runPrefixOuter_bind,runAtPrefix_run,runPrefix_lift]
  cases body.run w <;> rfl

theorem prefill_run_with (count : Nat)
    (work : SeccompWorld → TaskWorld → Except String (SeccompWorld × TaskWorld)) (w : World) :
    (prefillBodyWith count work).run w =
      if count > 0 then
        match work w.seccomp w.tasks with
        | .ok (seccomp,tasks)=>.ok ((),{w with seccomp,tasks})
        | .error reason=>.error (.invariant reason)
      else .ok ((),w) := by
  by_cases positive : count > 0
  · cases performed : work w.seccomp w.tasks <;>
      simp [prefillBodyWith,positive,performed]
  · simp [prefillBodyWith,positive]

theorem prefill_run (count : Nat) (w : World) :
    (prefillBody count).run w =
      if count > 0 then
        match Env.seccompPrefill count w.seccomp w.tasks with
        | .ok (seccomp,tasks)=>.ok ((),{w with seccomp,tasks})
        | .error reason=>.error (.invariant reason)
      else .ok ((),w) := prefill_run_with count (Env.seccompPrefill count) w

theorem prefill_source (count : Nat) (w : World) :
    ConservationRunner.prefillWith count w (pure : World → PrefixOuter Event World) =
      (do let out ← runAtPrefix 0 w (liftPrefix (prefillBody count));pure out.2) := by
  funext h
  change runPrefixOuter (ConservationRunner.prefillWith count w pure) h =
    runPrefixOuter (do let out ← runAtPrefix 0 w (liftPrefix (prefillBody count));pure out.2) h
  rw [setup_run,prefill_run]
  unfold ConservationRunner.prefillWith
  split
  · cases Env.seccompPrefill count w.seccomp w.tasks <;> rfl
  · rfl

def bootPrefix (foreign : Bool) : Leanux.M Unit := do
  Net.Fib.bootTables
  if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables

theorem boot_body_true (foreign : Bool) : bootBody true foreign =
    (bootPrefix foreign >>= fun _=>modifyAmbient fun a=>{a with steps:=#[],envCalls:=[]}) := by
  simp only [bootBody,bootPrefix,ite_true,bind_assoc]
  congr 1
  funext ignored
  cases foreign <;> rfl

theorem boot_source (net foreign : Bool) (w : World) :
    ConservationRunner.bootWith net foreign w (pure : World → PrefixOuter Event World) =
      (do let out ← runAtPrefix 0 w (liftPrefix (bootBody net foreign));pure out.2) := by
  funext h
  change runPrefixOuter (ConservationRunner.bootWith net foreign w pure) h =
    runPrefixOuter (do let out ← runAtPrefix 0 w (liftPrefix (bootBody net foreign));pure out.2) h
  rw [setup_run]
  cases net with
  | false => rfl
  | true =>
      unfold ConservationRunner.bootWith
      simp only [ite_true]
      change runPrefixOuter (match (bootPrefix foreign).run w with
        | .ok (_,v)=>pure {v with ambient:={v.ambient with steps:=#[],envCalls:=[]}}
        | .error reason=>throw (0,reason)) h = _
      rw [boot_body_true,StateT.run_bind]
      cases performed : (bootPrefix foreign).run w <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PrefixStore
