import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumePointSource

/-! Factor the existing receipts around the original native call. The saved
world is captured before the call, not chosen from historical validity. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

theorem receipt_factor (body : PrefixM Event α) (record : RunWitness α → Event) :
    receiptObserved body record = (do
      let before ← liftPrefix (get : Leanux.M World)
      let value ← body
      let after ← liftPrefix (get : Leanux.M World)
      emitPrefix (record ⟨value,before,after⟩)
      pure value) := by
  funext w h
  change runPrefix (receiptObserved body record) w h = runPrefix (do
    let before ← liftPrefix (get : Leanux.M World)
    let value ← body
    let after ← liftPrefix (get : Leanux.M World)
    emitPrefix (record ⟨value,before,after⟩)
    pure value) w h
  rw [runPrefix_receiptObserved,runPrefix_bind]
  change _ = runPrefix (body >>= _) w h
  rw [runPrefix_bind]
  cases performed : runPrefix body w h with
  | mk result last =>
    cases result with
    | error reason => rfl
    | ok pair => rcases pair with ⟨value,u⟩; rfl

theorem wg_receipt_factor (body : WG.M α) (record : WGRunWitness α → Event) :
    liftWGObserver (receiptWGObserved (liftWGPrefix body) record) = (do
      let before ← liftPrefix (get : Leanux.M World)
      let value ← wg body
      let after ← liftPrefix (get : Leanux.M World)
      emitPrefix (record ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩)
      pure value) := by
  funext w h
  change runPrefix (liftWGObserver (receiptWGObserved (liftWGPrefix body) record)) w h = runPrefix (do
    let before ← liftPrefix (get : Leanux.M World)
    let value ← wg body
    let after ← liftPrefix (get : Leanux.M World)
    emitPrefix (record ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩)
    pure value) w h
  rw [liftWGObserver_run,runWGPrefix_receiptWGObserved,runWGPrefix_lift,runPrefix_bind]
  change _ = runPrefix (wg body >>= _) w h
  rw [runPrefix_bind,liftWGObserver_run,runWGPrefix_lift]
  cases performed : (body.run w.wg).run w.ambient with
  | error reason => rfl
  | ok pair => rcases pair with ⟨⟨value,u⟩,a⟩; rfl

theorem counter_factor (skb : SkbId) (packet : RxPacket) :
    hooks.counterCheck skb packet = (do
      let before ← liftPrefix (get : Leanux.M World)
      let value ← wg (counterValidate packet.keypair packet.nonce)
      let after ← liftPrefix (get : Leanux.M World)
      emitPrefix (.old (.replay ⟨skb,packet,⟨value,before,after⟩⟩))
      pure value) := by
  change focusPrefix Event.old old? (TransportDriver.counter Journal.Event.replay skb packet) = _
  unfold TransportDriver.counter
  rw [Staged.Origins.focused_product_receipt,receipt_factor]
  rfl

theorem confirmation_factor (pid : PeerId) (kid : KeypairId) :
    liftWGObserver (hooks.confirmation pid kid) = (do
      let before ← liftPrefix (get : Leanux.M World)
      let value ← wg (receivedWithKeypair pid kid)
      let after ← liftPrefix (get : Leanux.M World)
      emitPrefix (.old (.responder (.confirmed pid kid
        ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩)))
      pure value) := by
  change liftWGObserver (CausalJournal.state (Journal.confirmation pid kid)) = _
  unfold state Journal.confirmation HandshakeSecurity.Responder.DriverCuts.confirmation
  rw [Staged.Origins.focused_native_receipt,Staged.Origins.focused_native_receipt,wg_receipt_factor]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
