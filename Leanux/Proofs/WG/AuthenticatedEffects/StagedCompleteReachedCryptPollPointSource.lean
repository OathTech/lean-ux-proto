import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumePointCapture

/-! The encryption-ring poll has two reads, its actual ring-pointer write
and two passive receipts. The fixed source tree exposes every one of those
boundaries and has no deeper callback. Ring aliases are not packet owners. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CryptPoll.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Queues TransmitSecurity CausalJournal
set_option maxRecDepth 4096
abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)

theorem runPrefix_focus (encode : E → F) (decode : F → Option E) (body : PrefixM E α)
    (w : World) (h : List F) :
    runPrefix (focusPrefix encode decode body) w h =
      let out := runPrefix body w (h.filterMap decode)
      (out.1,h ++ (out.2.drop (h.filterMap decode).length).map encode) := rfl

def observed : PrefixM Event (Option (List SkbId)) :=
  receiptObserved (do
    let item ← liftPrefix (liftWG TxRing.pollSource)
    emitPrefix (.old (.ring (.polled item)))
    pure item) (fun receipt => .old (.polled receipt))

theorem observed_eq : hooks.poll = observed := by
  funext w h
  change runPrefix (product Journal.poll) w h = runPrefix observed w h
  unfold product Journal.poll TxRing.poll Ring.Source.poll observed
  simp only [runPrefix_focus,runPrefix_receiptObserved,
    runPrefix_bind,runPrefix_lift,runPrefix_emit,runPrefix_pure]
  cases performed : (liftWG TxRing.pollSource).run w with
  | error reason => simp
  | ok pair =>
      obtain ⟨item,u⟩ := pair
      simp

def source : PrefixM Event (Option (List SkbId)) := do
  let before ← liftPrefix (get : Leanux.M World)
  let device ← liftPrefix (liftWG getDev)
  liftPrefix (liftWG (modifyDev fun d => {d with encryptQueue := device.encryptQueue.consume.2}))
  let item := device.encryptQueue.consume.1
  emitPrefix (.old (.ring (.polled item)))
  let after ← liftPrefix (get : Leanux.M World)
  emitPrefix (.old (.polled ⟨item,before,after⟩))
  pure item

theorem source_eq : hooks.poll = source := by
  rw [observed_eq]
  unfold observed
  rw [Consume.Points.receipt_factor]
  unfold TxRing.pollSource
  simp only [liftWG_bind,liftWG_pure,Service.Points.lift_bind,Service.Points.lift_pure,bind_assoc,pure_bind]
  rfl

inductive Native where
  | world
  | device
  | install (ring : PtrRing (List SkbId))
  | polled (item : Option (List SkbId))
  | receipt (value : RunWitness (Option (List SkbId)))

def Native.Result : Native → Type
  | .world => World
  | .device => Device
  | _ => Unit

def Native.action (token : Native) : PrefixM Event token.Result := match token with
  | .world => liftPrefix (get : Leanux.M World)
  | .device => liftPrefix (liftWG getDev)
  | .install ring => liftPrefix (liftWG (modifyDev fun d => {d with encryptQueue := ring}))
  | .polled item => emitPrefix (.old (.ring (.polled item)))
  | .receipt value => emitPrefix (.old (.polled value))

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native) : Shape token.action
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

noncomputable def canonical : Shape hooks.poll := by
  rw [source_eq]
  exact .bind (.native .world) (fun before =>
    .bind (.native .device) (fun device =>
    .bind (.native (.install device.encryptQueue.consume.2)) (fun _ =>
    .bind (.native (.polled device.encryptQueue.consume.1)) (fun _ =>
    .bind (.native .world) (fun after =>
    .bind (.native (.receipt ⟨device.encryptQueue.consume.1,before,after⟩)) (fun _ =>
    .pure device.encryptQueue.consume.1))))))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CryptPoll.Points
