import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReturnPath

/-! The original post-transmit guard chooses the crypt branch before any
worker callback. Its prefix retains the original mixed-work refusal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal

def front : PrefixM Event (Option Bool) := do
  let some d := (← liftPrefix getWG).dev | return none
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    liftPrefix (unsupported "wg_xmit queued crypt work and a handshake (their order)")
  liftPrefix (modifyWG fun w=>{w with queuedThisCall:=[]})
  return some crypt

def cryptTail : PrefixM Event Unit := do
  Driver.cryptObserved hooks
  let d ← liftPrefix (liftWG getDev)
  liftPrefix (Env.requireDrained "wg_xmit queued" [!d.encryptQueue.empty,!d.txWorkQueue.isEmpty])

def tail : Option Bool → PrefixM Event Unit
  | none => pure ()
  | some crypt => do
    if crypt then cryptTail
    Driver.sendWorkersObserved hooks

theorem front_factor : Driver.afterXmitObserved hooks=(front >>= tail) := by
  unfold Driver.afterXmitObserved front tail cryptTail
  simp only [bind_assoc]
  congr 1
  funext w
  cases w.dev <;> simp only [pure_bind]
  rename_i device
  split <;> simp only [pure_bind,bind_assoc]
  all_goals congr 1

def sendPrefix : PrefixM Event Bool := do
  match ← front with
  | none => pure false
  | some crypt =>
    if crypt then cryptTail
    pure true

theorem send_factor : Driver.afterXmitObserved hooks=(sendPrefix >>= fun entered=>
    if entered then Driver.sendWorkersObserved hooks else pure ()) := by
  rw [front_factor]
  unfold sendPrefix
  rw [bind_assoc]
  congr 1
  funext selected
  cases selected with
  | none => rfl
  | some crypt =>
    unfold tail
    cases crypt <;> simp only [Bool.false_eq_true,↓reduceIte,pure_bind,bind_assoc]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
