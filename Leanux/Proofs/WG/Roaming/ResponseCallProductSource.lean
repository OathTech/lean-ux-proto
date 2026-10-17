import Leanux.Proofs.WG.Roaming.ResponseCallSource
import Leanux.Proofs.WG.Roaming.ResponseCallProductModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

def responseLoad : Leanux.M Bool := liftWG Roaming.responseLoad

/-- Actual load-test source with an unrestricted product continuation. -/
def receiveLoadThen (next : Bool → Leanux.M Unit) : Leanux.M Unit := do
  let mut underLoad := false
  let queueLen := (← liftWG getDev).handshakeQueueLen
  if ← liftWG (branchCmp .hsUnderLoad (queueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
      (Int.ofNat queueLen) (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8))) then
    let now ← liftWG (hiddenClock64 .underLoadNow)
    liftWG (modify fun w => {w with lastUnderLoad := some now})
    underLoad := true
  else if ← liftWG (branch .hsWasUnderLoad (← liftWG (get : WG.M WGWorld)).lastUnderLoad.isSome) then
    let some last := (← liftWG (get : WG.M WGWorld)).lastUnderLoad | invariant "unreachable"
    let (expired, lhs, now) ← liftWG (birthdateTest last 1)
    underLoad := !expired
    if ← liftWG (branchCmp .hsDecayExpired expired lhs now) then
      liftWG (modify fun w => {w with lastUnderLoad := none})
  next underLoad

theorem responseLoad_source (next : Bool → Leanux.M Unit) :
    (responseLoad >>= next) = receiveLoadThen next := by
  have liftWG_bind_variant {α β : Type} (a : WG.M α) (f : α → WG.M β) :
      liftWG (a >>= f) = (liftWG a >>= fun x => liftWG (f x)) := by
    funext w
    dsimp only [liftWG, StateT.run, StateT.bind, StateT.pure, StateT.map,
      Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
    cases run : a w.wg w.ambient with
    | error err => rfl
    | ok pair =>
      rcases pair with ⟨⟨out, current⟩, after⟩
      rfl
  have lift_pure {α : Type} (x : α) : liftWG (pure x : WG.M α) = pure x := rfl
  have lift_ite {α : Type} (p : Prop) [Decidable p] (a b : WG.M α) :
      liftWG (if p then a else b) = if p then liftWG a else liftWG b := by split <;> rfl
  have bind_if {α β : Type} (p : Prop) [Decidable p]
      (a b : Leanux.M α) (f : α → Leanux.M β) :
      ((if p then a else b) >>= f) = if p then a >>= f else b >>= f := by split <;> rfl
  simp only [responseLoad, Roaming.responseLoad, receiveLoadThen, liftWG_bind_variant,
    lift_pure, lift_ite, bind_assoc, pure_bind, bind_if]
  congr 1
  funext d
  congr 1
  funext loaded
  cases loaded <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  congr 1
  funext g
  congr 1
  funext wasLoaded
  cases wasLoaded <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  congr 1
  funext g
  cases g.lastUnderLoad with
  | none => rfl
  | some last =>
    simp only [liftWG_bind_variant, lift_pure, lift_ite, bind_assoc, pure_bind, bind_if]

def responsePacketPrefix (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    Leanux.M (Option ResponseCallCut) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.responsePacketPrefix msg src underLoad)
  pure (out.map (restoreResponseCallCut fixture))

def responseAfterSetter (msg : List UInt8) (pid : PeerId) : Leanux.M Unit :=
  liftWG (Roaming.responseAfterSetter msg pid)

def responseCallSuffix (msg : List UInt8) (src : SkbSource) : Option ResponseCallCut → Leanux.M Unit
  | none => pure ()
  | some cut => liftWG (do
    setPeerEndpointFromSkb cut.consumed.input.pid src
    Roaming.responseAfterSetter msg cut.consumed.input.pid)

def responseCallPrefix (msg : List UInt8) (src : SkbSource) : Leanux.M (Option ResponseCallCut) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.responseCallPrefix msg src)
  pure (out.map (restoreResponseCallCut fixture))

def observedResponseHandshake (msg : List UInt8) (src : SkbSource) :
    Leanux.M (Campaign2.Product.Outcome (Option ResponseCallCut)) := do
  let observed ← Campaign2.Product.inspect (responseCallPrefix msg src)
  liftWG (receiveHandshakePacket msg src)
  pure observed

theorem observedResponseHandshake_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedResponseHandshake msg src; pure ()) = liftWG (receiveHandshakePacket msg src) := by
  funext w
  change (((liftWG (receiveHandshakePacket msg src)).run w >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((responseCallPrefix msg src).run w), out.2))
      >>= fun out => Except.ok ((), out.2)) = (liftWG (receiveHandshakePacket msg src)).run w
  cases run : (liftWG (receiveHandshakePacket msg src)).run w with
  | error e => rfl
  | ok pair => rcases pair with ⟨value, final⟩; cases value; rfl

theorem responsePacket_source (msg : List UInt8) (src : SkbSource) (underLoad : Bool)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (responsePacketPrefix msg src underLoad >>= responseCallSuffix msg src) =
      liftWG (Index.receivePacketBody msg src underLoad) := by
  rw [← Roaming.responsePacket_source msg src underLoad kind]
  funext w
  dsimp only [responsePacketPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases run : ((Roaming.responsePacketPrefix msg src underLoad).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at run; rw [run]
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, after⟩
    simp only [StateT.run] at run
    rw [run]
    cases out <;> rfl

theorem receiveHandshakePacket_response (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (responseCallPrefix msg src >>= responseCallSuffix msg src) = liftWG (receiveHandshakePacket msg src) := by
  rw [← Roaming.receiveHandshakePacket_response msg src kind]
  funext w
  dsimp only [responseCallPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases run : ((Roaming.responseCallPrefix msg src).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at run; rw [run]
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, after⟩
    simp only [StateT.run] at run
    rw [run]
    cases out <;> rfl

def responseCallTranscript (msg : List UInt8) (src : SkbSource) :
    Leanux.M (Campaign2.Product.Outcome (Option ResponseCallCut)) := do
  let candidate ← responseCallPrefix msg src
  let atCut ← Campaign2.Product.read
  responseCallSuffix msg src candidate
  return .ok (candidate, atCut)

theorem observedResponseHandshake_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    observedResponseHandshake msg src = responseCallTranscript msg src := by
  funext w
  change ((liftWG (receiveHandshakePacket msg src)).run w >>= fun out =>
    Except.ok (Campaign2.Product.observeResult ((responseCallPrefix msg src).run w), out.2)) = _
  rw [← receiveHandshakePacket_response msg src kind]
  change (((responseCallPrefix msg src).run w >>= fun out =>
    (responseCallSuffix msg src out.1).run out.2) >>= fun out =>
      Except.ok (Campaign2.Product.observeResult ((responseCallPrefix msg src).run w), out.2)) =
    ((responseCallPrefix msg src).run w >>= fun cut =>
      (responseCallSuffix msg src cut.1).run cut.2 >>= fun out =>
        Except.ok (Except.ok (cut.1, Campaign2.Product.snapshot cut.2), out.2))
  cases hp : (responseCallPrefix msg src).run w with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    cases hs : (responseCallSuffix msg src candidate).run atCut <;> rfl

end Leanux.Proofs.WG.Roaming.Product
