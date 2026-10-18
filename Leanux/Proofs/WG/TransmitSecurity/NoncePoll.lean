import Leanux.Proofs.WG.TransmitSecurity.NonceReceive
import Leanux.Proofs.WG.TransmitSecurity.NoncePollFrames
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationPollSource
import Leanux.Proofs.Logged.PrefixGro

/-! The original product-state receive poll, with the real GRO callback kept
explicit. Receive-triggered staging and callback-triggered sends share one
nonce history; the callback contract is discharged by the stack caller. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open HandshakeSecurity.Confirmation.Poll

def pollObserved (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → PrefixM Allocation Unit) : PrefixM Allocation Nat :=
  sourceWith (fun a => liftWGObserver (liftWGPrefix a))
    (fun pkt => liftWGObserver (liftWGPrefix (counterValidate pkt.keypair pkt.nonce)))
    (fun peer pkt ep => liftWGObserver (consumeObserved peer pkt ep))
    (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget

theorem poll_source (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → Leanux.M Unit) :
    rxPoll pid budget toStack =
      sourceWith liftWG (fun pkt => liftWG (counterValidate pkt.keypair pkt.nonce))
        (fun peer pkt ep => liftWG (consumeDataDone peer pkt ep))
        (napiGroReceive toStack) (napiGroFlushAll toStack) pid budget := by
  simp only [rxPoll,sourceWith,liftWG_bind,bind_assoc]
  rfl

theorem pollObserved_erases (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM Allocation Unit)
    (original : List (List UInt8) → Leanux.M Unit)
    (callbacks : ∀ packets, ErasesPrefix (callback packets) (original packets)) :
    ErasesPrefix (pollObserved pid budget callback) (rxPoll pid budget original) := by
  rw [poll_source]
  unfold pollObserved sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | exact liftWGObserver_erases (consumeObserved_erases _ _ _)
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact napiGroReceivePrefix_erases _ _ callbacks _ _
    | with_reducible exact napiGroFlushAllPrefix_erases _ _ callbacks _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_forIn
    | (session_origin_intro_forall; try dsimp only)
    | split


private theorem poll_loop {α β : Type} (xs : List α) (b : β)
    (f : α → β → PrefixM Allocation (ForInStep β))
    (hf : ∀ x b, PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (f x b)) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (forIn xs b f) :=
  PrefixEnsures.forInInvariant xs b f (fun _ h w => Inv (view w.wg) h) List.Nodup
    (fun _ _ _ hi => hi.nodup) hf

open Lean Meta Elab Tactic in
elab "nonce_product_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  let action ←
    if target.isAppOf ``PrefixPreserves then pure args.back!
    else if target.isAppOf ``PrefixEnsures then pure args[args.size - 2]!
    else throwError "not a product-prefix contract"
  let .const actual _ := action.consumeMData.headBeta.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

private theorem product_safe {α : Type} {g : WGPrefix Allocation α}
    (safe : StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup g) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (liftWGObserver g) :=
  safe.liftWGObserver

open Frames in
theorem pollObserved_safe (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM Allocation Unit)
    (callbacks : ∀ packets, PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (callback packets)) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (pollObserved pid budget callback) := by
  unfold pollObserved sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (nonce_product_head napiGroReceivePrefix
       exact napiGroReceivePrefix_preserves callback (fun _ _ hi => hi.nodup) callbacks _ _)
    | (nonce_product_head napiGroFlushAllPrefix
       exact napiGroFlushAllPrefix_preserves callback (fun _ _ hi => hi.nodup) callbacks _)
    | (nonce_product_head liftWGObserver
       apply product_safe
       first
         | (nonce_source_head consumeObserved; exact consumeObserved_safe _ _ _)
         | (apply Frames.lift_preserves; intro h
            try unfold WG.andM
            try simp (config := {zeta := false}) only [branch,invariant,unsupported]
            repeat' nonce_poll_native_step h))
    | (first | nonce_product_head Pure.pure | nonce_product_head pure
       exact PrefixPreserves.pure (fun _ _ hi => hi.nodup) _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ForIn.forIn; apply poll_loop)
    | split
    | (session_origin_intro_forall; try dsimp only)

end Leanux.Proofs.WG.TransmitSecurity.Nonce
